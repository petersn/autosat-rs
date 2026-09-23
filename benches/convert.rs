//! Benchmarks `convert_to_cnf` over the shared suite of test functions.
//!
//!   cargo bench -- [FILTER...] [--min-bits N] [--max-bits N] [--big] [--huge] [--repeat N]
//!                  [--reference] [--reference-only] [--golden] [--list]
//!
//! FILTERs are substrings of case names (or exact names, if prefixed with `=`). `--reference` also runs the original
//! implementation and checks that the outputs are identical. `--golden` prints
//! lines in the format of `tests/golden.txt`.

#[path = "../tests/common/mod.rs"]
mod common;

use std::io::Write;
use std::time::{Duration, Instant};

use common::cases::{all_cases, big_cases, huge_cases, Case};

fn time<T>(repeat: usize, mut f: impl FnMut() -> T) -> (T, Duration) {
  let mut best = Duration::MAX;
  let mut result = None;
  for _ in 0..repeat {
    let start = Instant::now();
    result = Some(f());
    best = best.min(start.elapsed());
  }
  (result.unwrap(), best)
}

fn fmt(d: Duration) -> String {
  let s = d.as_secs_f64();
  match s {
    s if s < 1e-3 => format!("{:.1}µs", s * 1e6),
    s if s < 1.0 => format!("{:.2}ms", s * 1e3),
    s => format!("{:.2}s", s),
  }
}

fn main() {
  let mut filters = vec![];
  let (mut min_bits, mut max_bits, mut repeat) = (0, usize::MAX, 1);
  let (mut big, mut reference, mut reference_only, mut golden) = (false, false, false, false);
  let (mut list, mut huge) = (false, false);
  let mut args = std::env::args().skip(1);
  while let Some(arg) = args.next() {
    let mut num = || args.next().and_then(|s| s.parse().ok()).expect("expected a number");
    match arg.as_str() {
      "--bench" => {}
      "--min-bits" => min_bits = num(),
      "--max-bits" => max_bits = num(),
      "--repeat" => repeat = num(),
      "--big" => big = true,
      "--huge" => huge = true,
      "--reference" => reference = true,
      "--reference-only" => reference_only = true,
      "--golden" => golden = true,
      "--list" => list = true,
      _ => filters.push(arg),
    }
  }

  let mut cases: Vec<Case> = all_cases();
  if big {
    cases.extend(big_cases());
  }
  if huge {
    cases.extend(huge_cases());
  }
  cases.retain(|c| {
    (min_bits..=max_bits).contains(&c.bits())
      && (filters.is_empty()
        || filters.iter().any(|f| match f.strip_prefix('=') {
          Some(exact) => c.name == exact,
          None => c.name.contains(f.as_str()),
        }))
  });

  if list {
    for case in &cases {
      println!("{} {}", case.name, case.bits());
    }
    return;
  }

  if !golden {
    println!(
      "{:<18} {:>4} {:>8} {:>9} {:>10} {:>10} {:>9}",
      "case", "bits", "clauses", "literals", "time", "reference", "speedup"
    );
  }
  let mut total = Duration::ZERO;
  let mut total_reference = Duration::ZERO;
  for case in &cases {
    let run_new = || autosat::convert_to_cnf(case.num_inputs, case.num_outputs, &case.f);
    let run_reference =
      || common::reference::convert_to_cnf(case.num_inputs, case.num_outputs, &case.f);
    let (cnf, t_new) = match reference_only {
      true => time(repeat, run_reference),
      false => time(repeat, run_new),
    };
    total += t_new;
    let literals: usize = cnf.iter().map(|c| c.len()).sum();
    if golden {
      println!("{} {} {:016x} # {}", case.name, cnf.len(), common::fingerprint(&cnf), fmt(t_new));
      continue;
    }
    print!(
      "{:<18} {:>4} {:>8} {:>9} {:>10}",
      case.name,
      case.bits(),
      cnf.len(),
      literals,
      fmt(t_new)
    );
    if reference && !reference_only {
      std::io::stdout().flush().unwrap();
      let (ref_cnf, t_ref) = time(1, run_reference);
      total_reference += t_ref;
      print!(" {:>10} {:>8.1}x", fmt(t_ref), t_ref.as_secs_f64() / t_new.as_secs_f64());
      if ref_cnf != cnf {
        print!("  MISMATCH (reference has {} clauses)", ref_cnf.len());
      }
    }
    println!();
  }
  if !golden {
    print!("{:<44} {:>10}", "total", fmt(total));
    if reference && !reference_only {
      print!(
        " {:>10} {:>8.1}x",
        fmt(total_reference),
        total_reference.as_secs_f64() / total.as_secs_f64()
      );
    }
    println!();
  }
}
