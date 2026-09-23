//! A suite of functions to convert, shared by the tests and the benchmarks.
//!
//! Every case is tabulated up front, so the cost of evaluating `f` is the same
//! (and negligible) no matter how the function is defined.
#![allow(dead_code)]

use autosat::SatOutput;

pub struct Case {
  pub name:        String,
  pub num_inputs:  usize,
  pub num_outputs: usize,
  pub f:           Box<dyn Fn(&[bool]) -> SatOutput + Send + Sync>,
}

impl Case {
  pub fn bits(&self) -> usize {
    self.num_inputs + self.num_outputs
  }
}

pub fn to_num(bits: &[bool]) -> u64 {
  bits.iter().rev().fold(0, |acc, &b| (acc << 1) | b as u64)
}

pub fn to_bits(x: u64, n: usize) -> Vec<bool> {
  (0..n).map(|i| (x >> i) & 1 == 1).collect()
}

pub enum Out {
  Val(u64),
  DontCare,
  Impossible,
}

fn mask(bits: usize) -> u64 {
  (1u64 << bits) - 1
}

fn tabulate(
  name: impl Into<String>,
  num_inputs: usize,
  num_outputs: usize,
  mut f: impl FnMut(u64) -> Out,
) -> Case {
  let table: Vec<SatOutput> = (0..1u64 << num_inputs)
    .map(|x| match f(x) {
      Out::Val(y) => {
        assert!(y >> num_outputs == 0, "output {} doesn't fit in {} bits", y, num_outputs);
        SatOutput::Bits(to_bits(y, num_outputs))
      }
      Out::DontCare => SatOutput::DontCare,
      Out::Impossible => SatOutput::ImpossibleInputs,
    })
    .collect();
  Case {
    name: name.into(),
    num_inputs,
    num_outputs,
    f: Box::new(move |input| table[to_num(input) as usize].clone()),
  }
}

fn func(name: impl Into<String>, ni: usize, no: usize, f: impl Fn(u64) -> u64) -> Case {
  tabulate(name, ni, no, |x| Out::Val(f(x)))
}

// ===== Structured functions =====

pub fn and(k: usize) -> Case {
  func(format!("and_{}", k), k, 1, |x| (x == mask(k)) as u64)
}

pub fn or(k: usize) -> Case {
  func(format!("or_{}", k), k, 1, |x| (x != 0) as u64)
}

pub fn xor(k: usize) -> Case {
  func(format!("xor_{}", k), k, 1, |x| (x.count_ones() & 1) as u64)
}

pub fn majority(k: usize) -> Case {
  func(format!("maj_{}", k), k, 1, |x| (2 * x.count_ones() as usize > k) as u64)
}

/// k-bit + k-bit -> (k+1)-bit.
pub fn add(k: usize) -> Case {
  func(format!("add_{}", k), 2 * k, k + 1, |x| (x & mask(k)) + (x >> k))
}

/// k-bit + k-bit + carry-in -> (k+1)-bit.
pub fn add_with_carry(k: usize) -> Case {
  func(format!("add_cin_{}", k), 2 * k + 1, k + 1, |x| {
    (x & mask(k)) + ((x >> k) & mask(k)) + (x >> (2 * k))
  })
}

/// k-bit * k-bit -> 2k-bit.
pub fn mul(k: usize) -> Case {
  func(format!("mul_{}", k), 2 * k, 2 * k, |x| (x & mask(k)) * (x >> k))
}

/// Squaring: k-bit -> 2k-bit.
pub fn square(k: usize) -> Case {
  func(format!("square_{}", k), k, 2 * k, |x| x * x)
}

/// Population count of k bits.
pub fn popcount(k: usize) -> Case {
  let out_bits = 64 - (k as u64).leading_zeros() as usize;
  func(format!("popcount_{}", k), k, out_bits, |x| x.count_ones() as u64)
}

/// Unsigned a < b for k-bit a and b.
pub fn less_than(k: usize) -> Case {
  func(format!("lt_{}", k), 2 * k, 1, |x| ((x & mask(k)) < (x >> k)) as u64)
}

/// k select bits, then 2^k data bits -> the selected data bit.
pub fn mux(k: usize) -> Case {
  func(format!("mux_{}", k), k + (1 << k), 1, |x| (x >> (k as u64 + (x & mask(k)))) & 1)
}

/// k-bit increment, wrapping.
pub fn increment(k: usize) -> Case {
  func(format!("inc_{}", k), k, k, |x| (x + 1) & mask(k))
}

/// Gray code to binary: every output bit is the XOR of a suffix of the input bits.
pub fn gray_to_binary(k: usize) -> Case {
  func(format!("gray2bin_{}", k), k, k, |g| {
    let mut b = 0;
    let mut g = g;
    while g != 0 {
      b ^= g;
      g >>= 1;
    }
    b
  })
}

/// Two k-bit numbers -> (min, max).
pub fn min_max(k: usize) -> Case {
  func(format!("minmax_{}", k), 2 * k, 2 * k, |x| {
    let (a, b) = (x & mask(k), x >> k);
    a.min(b) | (a.max(b) << k)
  })
}

/// Rotate k data bits left by an s-bit amount.
pub fn rotate(k: usize, s: usize) -> Case {
  func(format!("rot_{}_{}", k, s), k + s, k, |x| {
    let (data, amount) = (x & mask(k), (x >> k) % k as u64);
    ((data << amount) | (data >> (k as u64 - amount))) & mask(k)
  })
}

/// BCD digit -> seven-segment display, with inputs 10-15 as don't-cares.
pub fn bcd_to_7seg() -> Case {
  const SEGMENTS: [u64; 10] = [0x3f, 0x06, 0x5b, 0x4f, 0x66, 0x6d, 0x7d, 0x07, 0x7f, 0x6f];
  tabulate("bcd_7seg", 4, 7, |x| match SEGMENTS.get(x as usize) {
    Some(&s) => Out::Val(s),
    None => Out::DontCare,
  })
}

/// One-hot k bits -> index; any non-one-hot input is impossible.
pub fn onehot_encode(k: usize) -> Case {
  let out_bits = 64 - (k as u64 - 1).leading_zeros() as usize;
  tabulate(format!("onehot_enc_{}", k), k, out_bits, |x| match x.count_ones() {
    1 => Out::Val(x.trailing_zeros() as u64),
    _ => Out::Impossible,
  })
}

/// a (ka bits) / b (kb bits) -> (quotient, remainder); b = 0 is impossible.
pub fn divmod(ka: usize, kb: usize) -> Case {
  tabulate(format!("divmod_{}_{}", ka, kb), ka + kb, ka + kb, |x| {
    let (a, b) = (x & mask(ka), x >> ka);
    match b {
      0 => Out::Impossible,
      _ => Out::Val((a / b) | ((a % b) << ka)),
    }
  })
}

pub fn aes_sbox_table() -> [u8; 256] {
  // Multiplicative inverse in GF(2^8) followed by the AES affine transform.
  fn gf_mul(mut a: u8, mut b: u8) -> u8 {
    let mut p = 0;
    while b != 0 {
      if b & 1 != 0 {
        p ^= a;
      }
      a = (a << 1) ^ if a & 0x80 != 0 { 0x1b } else { 0 };
      b >>= 1;
    }
    p
  }
  let mut sbox = [0u8; 256];
  for x in 0..=255u8 {
    let inv = (1..=255u8).find(|&y| gf_mul(x, y) == 1).unwrap_or(0);
    sbox[x as usize] = inv
      ^ inv.rotate_left(1)
      ^ inv.rotate_left(2)
      ^ inv.rotate_left(3)
      ^ inv.rotate_left(4)
      ^ 0x63;
  }
  assert_eq!((sbox[0x00], sbox[0x01], sbox[0x53], sbox[0xff]), (0x63, 0x7c, 0xed, 0x16));
  sbox
}

pub fn aes_sbox() -> Case {
  let sbox = aes_sbox_table();
  func("aes_sbox", 8, 8, move |x| sbox[x as usize] as u64)
}

pub fn present_sbox() -> Case {
  const SBOX: [u64; 16] = [0xc, 5, 6, 0xb, 9, 0, 0xa, 0xd, 3, 0xe, 0xf, 8, 4, 7, 1, 2];
  func("present_sbox", 4, 4, |x| SBOX[x as usize])
}

// ===== Random functions =====

/// SplitMix64, so the suite doesn't need a dependency.
pub struct Rng(u64);

impl Rng {
  pub fn new(seed: u64) -> Self {
    Rng(seed)
  }

  pub fn next(&mut self) -> u64 {
    self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
    let mut z = self.0;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
    z ^ (z >> 31)
  }

  /// True with probability `percent` / 100.
  pub fn chance(&mut self, percent: u64) -> bool {
    self.next() % 100 < percent
  }
}

/// A uniformly random function, where each input is independently a don't-care
/// with probability `dont_care`% or impossible with probability `impossible`%.
pub fn random(ni: usize, no: usize, dont_care: u64, impossible: u64, seed: u64) -> Case {
  let mut name = format!("rand_{}x{}", ni, no);
  if dont_care > 0 {
    name += &format!("_dc{}", dont_care);
  }
  if impossible > 0 {
    name += &format!("_imp{}", impossible);
  }
  if seed != 0 {
    name += &format!("_s{}", seed);
  }
  let mut rng = Rng::new(seed ^ ((ni as u64) << 32) ^ ((no as u64) << 40) ^ (dont_care << 48) ^ (impossible << 56));
  tabulate(name, ni, no, |_| {
    let roll = rng.next() % 100;
    let value = rng.next() & mask(no);
    if roll < dont_care {
      Out::DontCare
    } else if roll < dont_care + impossible {
      Out::Impossible
    } else {
      Out::Val(value)
    }
  })
}

/// The full suite, in rough order of increasing size.
pub fn all_cases() -> Vec<Case> {
  let mut cases = vec![
    // Structured.
    present_sbox(),
    xor(7),
    majority(7),
    and(8),
    add(3),
    popcount(7),
    less_than(5),
    bcd_to_7seg(),
    onehot_encode(8),
    xor(11),
    majority(11),
    mul(3),
    mux(3),
    increment(6),
    gray_to_binary(6),
    min_max(3),
    or(12),
    add(4),
    xor(13),
    majority(13),
    add_with_carry(4),
    gray_to_binary(7),
    rotate(6, 2),
    popcount(11),
    less_than(7),
    square(5),
    and(15),
    xor(15),
    majority(15),
    add(5),
    mul(4),
    popcount(12),
    aes_sbox(),
    increment(8),
    gray_to_binary(8),
    min_max(4),
    onehot_encode(12),
    divmod(5, 3),
  ];
  // Random.
  for &(ni, no) in &[
    (4, 4), (5, 5), (6, 6), (10, 2), (7, 7), (12, 2), (10, 4),
    (8, 8), (15, 1), (14, 2), (12, 4), (4, 12),
  ] {
    cases.push(random(ni, no, 0, 0, 0));
  }
  cases.push(random(7, 7, 25, 0, 0));
  cases.push(random(7, 7, 0, 25, 0));
  cases.push(random(8, 8, 25, 0, 0));
  cases.push(random(8, 8, 0, 25, 0));
  cases.push(random(8, 8, 20, 20, 0));
  cases.sort_by_key(|c| c.bits());
  cases
}

/// Some bigger cases (17-18 bits), to see how far things can be pushed.
pub fn big_cases() -> Vec<Case> {
  vec![
    xor(16),
    majority(17),
    add(6),
    popcount(14),
    gray_to_binary(9),
    square(6),
    random(9, 9, 0, 0, 0),
    random(10, 8, 0, 0, 0),
    random(16, 2, 0, 0, 0),
  ]
  .into_iter()
  .filter(|c| c.bits() > 16)
  .collect()
}

/// Cases of 20 bits and up.
pub fn huge_cases() -> Vec<Case> {
  vec![
    xor(19),
    majority(19),
    mul(5),
    popcount(16),
    square(7),
    random(10, 10, 0, 0, 0),
    random(12, 8, 0, 0, 0),
    random(16, 4, 0, 0, 0),
    random(18, 2, 0, 0, 0),
    add(7),
    random(11, 11, 0, 0, 0),
    mul(6),
    random(12, 12, 0, 0, 0),
    add(8),
    random(13, 12, 0, 0, 0),
  ]
}
