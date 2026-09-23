use std::cmp::Reverse;
use std::collections::binary_heap::{BinaryHeap, PeekMut};
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicUsize, Ordering};
use std::sync::{Mutex, RwLock};

mod cache;
pub use cache::{convert_to_cnf_cached, convert_to_cnf_cached_in};

pub type SatLiteral = i32;
pub type SatClause = Vec<SatLiteral>;
pub type Cnf = Vec<SatClause>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SatOutput {
  Bits(Vec<bool>),
  DontCare,
  ImpossibleInputs,
}

// Bit i of a setting is variable i + 1. A clause over variables `s` rules out the
// cube of settings with `x & s == vals`, and is feasible if that cube has no
// allowed setting. For each clause length in turn, we greedily pick the feasible
// clause ruling out the most settings that aren't ruled out yet.

// The bits whose position has bit b clear.
const LOW_HALVES: [u64; 6] = [
  0x5555555555555555,
  0x3333333333333333,
  0x0f0f0f0f0f0f0f0f,
  0x00ff00ff00ff00ff,
  0x0000ffff0000ffff,
  0x00000000ffffffff,
];

// Gathers the bits of x whose position has bit j clear into the low 32 bits.
#[inline(always)]
fn compress_word(x: u64, j: usize) -> u64 {
  let mut x = x & LOW_HALVES[j];
  for s in j + 1..6 {
    x = (x | (x >> (1 << (s - 1)))) & LOW_HALVES[s];
  }
  x
}

// Software pdep.
#[inline(always)]
fn deposit(mut bits: usize, mut mask: usize) -> usize {
  let mut result = 0;
  while mask != 0 {
    if bits & 1 != 0 {
      result |= mask & mask.wrapping_neg();
    }
    bits >>= 1;
    mask &= mask - 1;
  }
  result
}

fn bitset_words(m: usize) -> usize {
  1 << m.saturating_sub(6)
}

// dst[c] = src[c with 0 inserted at bit j] op src[c with 1 inserted at bit j].
#[inline(always)]
fn fold<const OR: bool>(src: &[u64], m: usize, j: usize, dst: &mut [u64]) {
  let op = |a: u64, b: u64| if OR { a | b } else { a & b };
  if j >= 6 {
    let chunk = 1 << (j - 6);
    for (hi, out) in dst.chunks_exact_mut(chunk).enumerate() {
      let (a, b) = src[2 * hi * chunk..(2 * hi + 2) * chunk].split_at(chunk);
      for k in 0..chunk {
        out[k] = op(a[k], b[k]);
      }
    }
  } else if m <= 6 {
    let w = src[0];
    dst[0] = compress_word(op(w, w >> (1 << j)), j);
  } else {
    for (k, out) in dst.iter_mut().enumerate() {
      let (lo, hi) = (src[2 * k], src[2 * k + 1]);
      *out = compress_word(op(lo, lo >> (1 << j)), j)
        | (compress_word(op(hi, hi >> (1 << j)), j) << 32);
    }
  }
}

// The settings with x & s == vals, as a set of words and a mask within each word.
struct Cube {
  word_mask:  u64,
  fixed_word: usize,
  free_words: usize,
}

impl Cube {
  fn new(n: usize, s: usize, vals: usize) -> Self {
    let mut word_mask = match n {
      0..=5 => (1u64 << (1 << n)) - 1,
      _ => !0,
    };
    for b in 0..n.min(6) {
      if (s >> b) & 1 == 1 {
        word_mask &= match (vals >> b) & 1 {
          0 => LOW_HALVES[b],
          _ => !LOW_HALVES[b],
        };
      }
    }
    let all_words = (1 << n.saturating_sub(6)) - 1;
    Cube { word_mask, fixed_word: vals >> 6, free_words: all_words & !(s >> 6) }
  }

  #[inline(always)]
  fn for_each_word(&self, mut f: impl FnMut(usize)) {
    let mut sub = 0usize;
    loop {
      f(self.fixed_word | sub);
      sub = sub.wrapping_sub(self.free_words) & self.free_words;
      if sub == 0 {
        break;
      }
    }
  }

  fn count(&self, bits: &[u64]) -> u32 {
    let mut total = 0;
    self.for_each_word(|w| total += (bits[w] & self.word_mask).count_ones());
    total
  }

  fn remove_from(&self, bits: &mut [u64]) {
    self.for_each_word(|w| bits[w] &= !self.word_mask);
  }
}

fn swap_variables(bits: &mut [u64], j: usize, h: usize) {
  let stride = 1 << (h - 6);
  for w in 0..bits.len() {
    if w & stride == 0 {
      let (a, b) = (bits[w], bits[w | stride]);
      let t = ((a >> (1 << j)) ^ b) & LOW_HALVES[j];
      bits[w] = a ^ (t << (1 << j));
      bits[w | stride] = b ^ t;
    }
  }
}

// The settings not yet ruled out, in several layouts with different variables
// within each word, so a cube can be counted in whichever layout it's densest in.
struct Remaining {
  n:       usize,
  shifts:  Vec<usize>,
  layouts: Vec<Vec<u64>>,
}

impl Remaining {
  fn new(n: usize, bits: Vec<u64>) -> Self {
    let shifts: Vec<usize> = match n {
      0..=11 => vec![0],
      _ => (0..(n + 5) / 6).map(|k| (6 * k).min(n - 6)).collect(),
    };
    let layouts = shifts
      .iter()
      .map(|&shift| {
        let mut layout = bits.clone();
        if shift > 0 {
          for j in 0..6 {
            swap_variables(&mut layout, j, shift + j);
          }
        }
        layout
      })
      .collect();
    Remaining { n, shifts, layouts }
  }

  fn bits(&self) -> &[u64] {
    &self.layouts[0]
  }

  #[inline(always)]
  fn cube(&self, k: usize, s: usize, vals: usize) -> Cube {
    let shift = self.shifts[k];
    let swap = |x: usize| {
      let d = ((x >> shift) ^ x) & 63;
      x ^ d ^ (d << shift)
    };
    Cube::new(self.n, swap(s), swap(vals))
  }

  fn count(&self, s: usize, vals: usize) -> u32 {
    let best = (0..self.shifts.len())
      .min_by_key(|&k| ((s >> self.shifts[k]) & 63).count_ones())
      .unwrap();
    self.cube(best, s, vals).count(&self.layouts[best])
  }

  fn remove(&mut self, s: usize, vals: usize) {
    for k in 0..self.layouts.len() {
      let cube = self.cube(k, s, vals);
      cube.remove_from(&mut self.layouts[k]);
    }
  }
}

// (count, Reverse(key)), where key = (variable set << 32) | polarity is the tiebreak order.
type Candidate = (u32, Reverse<u64>);

type Buffers = (Vec<u64>, Vec<u64>);

// Finds the feasible clauses of length len that rule out a remaining setting.
struct CandidateSearch<'a> {
  n:          usize,
  len:        usize,
  disallowed: &'a [u64],
  remaining:  &'a Remaining,
}

impl CandidateSearch<'_> {
  // Variables >= undecided are in the clause iff they're in kept. The bitsets are
  // indexed by the undecided variables, then the kept ones.
  fn visit(
    &self,
    undecided: usize,
    kept: usize,
    feasible: &[u64],
    hits: &[u64],
    scratch: &mut [Buffers],
    out: &mut Vec<Candidate>,
  ) {
    let k = kept.count_ones() as usize;
    if undecided == 0 {
      self.collect(kept, feasible, hits, out);
      return;
    }
    let u = undecided - 1;
    if k < self.len {
      self.visit(u, kept | (1 << u), feasible, hits, scratch, out);
    }
    if u + k >= self.len {
      let (buffers, scratch) = scratch.split_first_mut().unwrap();
      if fold_both(feasible, hits, undecided + k, u, buffers) {
        self.visit(u, kept, &buffers.0, &buffers.1, scratch, out);
      }
    }
  }

  fn collect(&self, s: usize, feasible: &[u64], hits: &[u64], out: &mut Vec<Candidate>) {
    let polarity_mask = (1usize << self.len) - 1;
    for (word_index, (&f, &h)) in feasible.iter().zip(hits).enumerate() {
      let mut word = f & h;
      while word != 0 {
        let c = word_index * 64 + word.trailing_zeros() as usize;
        word &= word - 1;
        let count = self.remaining.count(s, deposit(c, s));
        let polarity = !c & polarity_mask;
        out.push((count, Reverse(((s as u64) << 32) | polarity as u64)));
      }
    }
  }

  fn visit_subtree(
    &self,
    undecided: usize,
    kept: usize,
    scratch: &mut [Buffers],
    out: &mut Vec<Candidate>,
  ) {
    let mut feasible = self.disallowed.to_vec();
    let mut hits = self.remaining.bits().to_vec();
    let mut buffers = (vec![], vec![]);
    let mut k = 0;
    for u in (undecided..self.n).rev() {
      if (kept >> u) & 1 == 1 {
        k += 1;
      } else {
        if !fold_both(&feasible, &hits, u + 1 + k, u, &mut buffers) {
          return;
        }
        std::mem::swap(&mut feasible, &mut buffers.0);
        std::mem::swap(&mut hits, &mut buffers.1);
      }
    }
    self.visit(undecided, kept, &feasible, &hits, scratch, out);
  }

  fn run(&self, threads: usize) -> Vec<Candidate> {
    if threads == 1 {
      let mut out = vec![];
      self.visit_subtree(self.n, 0, &mut vec![(vec![], vec![]); self.n], &mut out);
      return out;
    }
    // Split by which of the top variables are kept, biggest subtrees first.
    let top = self.n.min(7);
    let undecided = self.n - top;
    let mut subtrees: Vec<usize> = (0..1usize << top)
      .map(|t| t << undecided)
      .filter(|&kept| {
        let k = kept.count_ones() as usize;
        k <= self.len && k + undecided >= self.len
      })
      .collect();
    subtrees.sort_by_key(|&kept| Reverse(kept.count_ones()));
    let next = AtomicUsize::new(0);
    let results = Mutex::new(vec![]);
    std::thread::scope(|scope| {
      for _ in 0..threads {
        scope.spawn(|| {
          let mut scratch = vec![(vec![], vec![]); self.n];
          let mut out = vec![];
          while let Some(&kept) = subtrees.get(next.fetch_add(1, Ordering::Relaxed)) {
            self.visit_subtree(undecided, kept, &mut scratch, &mut out);
          }
          results.lock().unwrap().push(out);
        });
      }
    });
    results.into_inner().unwrap().concat()
  }
}

// Returns whether any cube is still both feasible and hitting.
fn fold_both(feasible: &[u64], hits: &[u64], m: usize, j: usize, out: &mut Buffers) -> bool {
  let words = bitset_words(m - 1);
  out.0.resize(words, 0);
  out.1.resize(words, 0);
  fold::<false>(feasible, m, j, &mut out.0);
  fold::<true>(hits, m, j, &mut out.1);
  out.0.iter().zip(&out.1).any(|(&f, &h)| f & h != 0)
}

fn bits_to_num(bits: &[bool]) -> usize {
  let mut result = 0;
  for i in 0..bits.len() {
    result += (bits[i] as usize) << i;
  }
  result
}

/// Returns a CNF over variables 1..=num_inputs (inputs) and then the outputs,
/// satisfied by exactly the input/output pairs that `f` allows.
pub fn convert_to_cnf(
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Cnf {
  let allowed = allowed_settings(num_inputs, num_outputs, f);
  cnf_from_allowed(num_inputs + num_outputs, &allowed)
}

fn allowed_settings(
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Vec<u64> {
  let n = num_inputs + num_outputs;
  assert!(n < 32, "too many bits: {}", n);
  let mut allowed = vec![0u64; bitset_words(n)];
  let mut input = vec![false; num_inputs];
  for i in 0..1usize << num_inputs {
    for (j, bit) in input.iter_mut().enumerate() {
      *bit = (i >> j) & 1 == 1;
    }
    match f(&input) {
      SatOutput::Bits(bits) => {
        assert!(bits.len() == num_outputs);
        let setting = i + (bits_to_num(&bits) << num_inputs);
        allowed[setting / 64] |= 1 << (setting % 64);
      }
      SatOutput::DontCare => {
        for j in 0..1usize << num_outputs {
          let setting = i + (j << num_inputs);
          allowed[setting / 64] |= 1 << (setting % 64);
        }
      }
      SatOutput::ImpossibleInputs => {}
    }
  }
  allowed
}

fn cnf_from_allowed(n: usize, allowed: &[u64]) -> Cnf {
  let all = Cube::new(n, 0, 0).word_mask;
  let disallowed: Vec<u64> = allowed.iter().map(|&w| !w & all).collect();
  let mut remaining_count: u32 = disallowed.iter().map(|w| w.count_ones()).sum();

  let mut cnf = Cnf::new();
  if remaining_count == 0 {
    return cnf;
  }
  if n == 0 {
    cnf.push(vec![]);
    return cnf;
  }

  let remaining = RwLock::new(Remaining::new(n, disallowed.clone()));
  let threads = match n {
    0..=15 => 1,
    _ => std::thread::available_parallelism().map_or(1, |t| t.get()),
  };
  for len in 1..=n {
    let candidates = {
      let remaining = remaining.read().unwrap();
      CandidateSearch { n, len, disallowed: &disallowed, remaining: &remaining }.run(threads)
    };
    // Parallel recounting only pays off for big cubes, and is slower past ~4 threads.
    let parallel = candidates.len() >= 1000 && n - len >= 8;
    let mut greedy = Greedy { len, remaining: &remaining, remaining_count, picks: 0 };
    if greedy.run(candidates, if parallel { threads.min(4) } else { 1 }, &mut cnf) {
      return cnf;
    }
    remaining_count = greedy.remaining_count;
  }
  unreachable!("every disallowed setting is covered by a clause of length n");
}

// (count, Reverse(key), number of picks when counted)
type Entry = (u32, Reverse<u64>, u32);

// Lazy greedy: counts only go down, so a top entry counted since the last pick is
// the true max. Stale entries can be recounted in any order, so we batch them.
struct Greedy<'a> {
  len:             usize,
  remaining:       &'a RwLock<Remaining>,
  remaining_count: u32,
  picks:           u32,
}

impl Greedy<'_> {
  fn cube(&self, key: u64) -> (usize, usize) {
    let (s, polarity) = ((key >> 32) as usize, (key & 0xffffffff) as usize);
    (s, deposit(!polarity & ((1 << self.len) - 1), s))
  }

  // Returns whether everything is ruled out.
  fn pick(&mut self, (count, Reverse(key), _): Entry, cnf: &mut Cnf) -> bool {
    let (s, vals) = self.cube(key);
    let mut clause = Vec::with_capacity(self.len);
    let mut vars = s;
    for _ in 0..self.len {
      let var = vars.trailing_zeros() as SatLiteral + 1;
      clause.push(if (vals >> (var - 1)) & 1 == 0 { var } else { -var });
      vars &= vars - 1;
    }
    cnf.push(clause);
    self.remaining.write().unwrap().remove(s, vals);
    self.remaining_count -= count;
    self.picks += 1;
    self.remaining_count == 0
  }

  fn run(&mut self, candidates: Vec<Candidate>, threads: usize, cnf: &mut Cnf) -> bool {
    let mut heap: BinaryHeap<Entry> =
      candidates.into_iter().map(|(count, key)| (count, key, 0)).collect();
    if threads == 1 {
      return self.run_serial(&mut heap, usize::MAX, cnf) == Some(true);
    }

    // Worker threads spin waiting for batches of cubes to count.
    const MAX_BATCH: usize = 1 << 12;
    let batch: RwLock<Vec<(usize, usize)>> = RwLock::new(Vec::with_capacity(MAX_BATCH));
    let results: Vec<AtomicU32> = (0..MAX_BATCH).map(|_| AtomicU32::new(0)).collect();
    let (next, done, epoch) = (AtomicUsize::new(0), AtomicUsize::new(0), AtomicUsize::new(0));
    let stop = AtomicBool::new(false);
    let remaining = self.remaining;
    let work = || {
      let batch = batch.read().unwrap();
      let remaining = remaining.read().unwrap();
      loop {
        let i = next.fetch_add(1, Ordering::Relaxed);
        if i >= batch.len() {
          break;
        }
        results[i].store(remaining.count(batch[i].0, batch[i].1), Ordering::Relaxed);
        done.fetch_add(1, Ordering::Release);
      }
    };
    std::thread::scope(|scope| {
      for _ in 1..threads {
        scope.spawn(|| {
          let mut seen = 0;
          while !stop.load(Ordering::Acquire) {
            let current = epoch.load(Ordering::Acquire);
            if current == seen {
              std::hint::spin_loop();
              continue;
            }
            seen = current;
            work();
          }
        });
      }

      let mut stale = Vec::with_capacity(MAX_BATCH);
      let mut batch_size = 16;
      let finished = loop {
        // If a few serial refreshes don't find a fresh top, recount growing batches.
        let picks = self.picks;
        match self.run_serial(&mut heap, 16, cnf) {
          Some(finished) => break finished,
          None if self.picks != picks => batch_size = 16,
          None => {}
        }
        stale.clear();
        while stale.len() < batch_size {
          match heap.peek() {
            Some(&(_, _, counted_at)) if counted_at != self.picks => stale.push(heap.pop().unwrap()),
            _ => break,
          }
        }
        {
          let mut batch = batch.write().unwrap();
          batch.clear();
          batch.extend(stale.iter().map(|&(_, Reverse(key), _)| self.cube(key)));
          next.store(0, Ordering::Relaxed);
          done.store(0, Ordering::Relaxed);
        }
        epoch.fetch_add(1, Ordering::Release);
        work();
        while done.load(Ordering::Acquire) < stale.len() {
          std::hint::spin_loop();
        }
        for (i, &(_, key, _)) in stale.iter().enumerate() {
          match results[i].load(Ordering::Relaxed) {
            0 => {}
            count => heap.push((count, key, self.picks)),
          }
        }
        batch_size = (2 * batch_size).min(MAX_BATCH);
      };
      stop.store(true, Ordering::Release);
      finished
    })
  }

  // Returns None after max_refreshes refreshes without a pick.
  fn run_serial(
    &mut self,
    heap: &mut BinaryHeap<Entry>,
    max_refreshes: usize,
    cnf: &mut Cnf,
  ) -> Option<bool> {
    let mut refreshes = 0;
    while let Some(mut top) = heap.peek_mut() {
      let (_, Reverse(key), counted_at) = *top;
      if counted_at != self.picks {
        if refreshes == max_refreshes {
          return None;
        }
        refreshes += 1;
        let (s, vals) = self.cube(key);
        match self.remaining.read().unwrap().count(s, vals) {
          0 => drop(PeekMut::pop(top)),
          count => *top = (count, Reverse(key), self.picks),
        }
        continue;
      }
      let entry = PeekMut::pop(top);
      if self.pick(entry, cnf) {
        return Some(true);
      }
      refreshes = 0;
    }
    Some(false)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn synthesize_xor_gate() {
    let xor_gate = convert_to_cnf(
      2, 1, |input| SatOutput::Bits(vec![input[0] ^ input[1]]),
    );
    assert_eq!(xor_gate, vec![
      vec![-1, -2, -3],
      vec![1, 2, -3],
      vec![1, -2, 3],
      vec![-1, 2, 3],
    ]);
  }

  #[test]
  fn compress_word_gathers_bits() {
    for j in 0..6 {
      for &x in &[0x0123456789abcdefu64, !0, 0xdeadbeef, 1 << 63] {
        let compressed = compress_word(x, j);
        assert_eq!(compressed >> 32, 0);
        for c in 0..32 {
          let pos = deposit(c, 63 & !(1 << j));
          assert_eq!((compressed >> c) & 1, (x >> pos) & 1);
        }
      }
    }
  }
}
