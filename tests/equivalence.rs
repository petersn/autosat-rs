mod common;

use autosat::{convert_to_cnf, Cnf, SatOutput};
use common::cases::{all_cases, random, Case, Rng};
use common::{fingerprint, reference};

fn convert(case: &Case) -> Cnf {
  convert_to_cnf(case.num_inputs, case.num_outputs, &case.f)
}

/// Checks that the settings satisfying `cnf` are exactly the allowed behaviors of `case`.
fn check_cnf_is_exact(case: &Case, cnf: &Cnf) {
  let n = case.bits();
  let mut allowed = vec![false; 1 << n];
  for i in 0..1usize << case.num_inputs {
    let input: Vec<bool> = (0..case.num_inputs).map(|j| (i >> j) & 1 == 1).collect();
    match (case.f)(&input) {
      SatOutput::Bits(bits) => {
        let out: usize = bits.iter().enumerate().map(|(j, &b)| (b as usize) << j).sum();
        allowed[i | (out << case.num_inputs)] = true;
      }
      SatOutput::DontCare => {
        for j in 0..1usize << case.num_outputs {
          allowed[i | (j << case.num_inputs)] = true;
        }
      }
      SatOutput::ImpossibleInputs => {}
    }
  }
  let mut ruled_out = vec![false; 1 << n];
  for clause in cnf {
    // Walk the settings that falsify this clause.
    let (mut fixed, mut vals) = (0usize, 0usize);
    for &literal in clause {
      let var = literal.unsigned_abs() as usize - 1;
      assert!(var < n && (fixed >> var) & 1 == 0, "{}: bad clause {:?}", case.name, clause);
      fixed |= 1 << var;
      vals |= ((literal < 0) as usize) << var;
    }
    let free = ((1 << n) - 1) & !fixed;
    let mut sub = 0usize;
    loop {
      let setting = vals | sub;
      assert!(!allowed[setting], "{}: clause {:?} rules out {}", case.name, clause, setting);
      ruled_out[setting] = true;
      sub = sub.wrapping_sub(free) & free;
      if sub == 0 {
        break;
      }
    }
  }
  for setting in 0..1 << n {
    assert!(
      allowed[setting] || ruled_out[setting],
      "{}: setting {} is not ruled out",
      case.name,
      setting
    );
  }
}

#[test]
fn every_case_is_exact() {
  for case in all_cases() {
    check_cnf_is_exact(&case, &convert(&case));
  }
}

/// `tests/golden.txt` has the fingerprints of the original implementation's output.
#[test]
fn matches_original_implementation_golden() {
  let golden = include_str!("golden.txt");
  let cases = all_cases();
  let mut checked = 0;
  for line in golden.lines().filter(|l| !l.starts_with('#') && !l.trim().is_empty()) {
    let fields: Vec<&str> = line.split_whitespace().collect();
    let case = cases.iter().find(|c| c.name == fields[0]).expect(fields[0]);
    let cnf = convert(case);
    assert_eq!(cnf.len().to_string(), fields[1], "{}: clause count", case.name);
    assert_eq!(format!("{:016x}", fingerprint(&cnf)), fields[2], "{}: fingerprint", case.name);
    checked += 1;
  }
  assert!(checked > 0);
}

#[test]
fn matches_original_implementation_small() {
  for case in all_cases().iter().filter(|c| c.bits() <= 10) {
    assert_eq!(convert(case), reference::convert_to_cnf(case.num_inputs, case.num_outputs, &case.f));
  }
}

#[test]
fn matches_original_implementation_random() {
  let mut rng = Rng::new(12345);
  for seed in 1..300 {
    let ni = (rng.next() % 7) as usize;
    let no = (rng.next() % 4) as usize;
    if ni + no == 0 {
      continue;
    }
    let (dont_care, impossible) = match rng.next() % 4 {
      0 => (0, 0),
      1 => (rng.next() % 60, 0),
      2 => (0, rng.next() % 60),
      _ => (rng.next() % 40, rng.next() % 40),
    };
    let case = random(ni, no, dont_care, impossible, seed);
    let cnf = convert(&case);
    assert_eq!(
      cnf,
      reference::convert_to_cnf(ni, no, &case.f),
      "{}",
      case.name
    );
    check_cnf_is_exact(&case, &cnf);
  }
}

#[test]
fn degenerate_functions() {
  // Everything allowed.
  assert_eq!(convert_to_cnf(3, 2, |_| SatOutput::DontCare), Cnf::new());
  // Nothing allowed.
  assert_eq!(convert_to_cnf(2, 1, |_| SatOutput::ImpossibleInputs), vec![vec![-1], vec![1]]);
  // No variables at all.
  assert_eq!(convert_to_cnf(0, 0, |_| SatOutput::Bits(vec![])), Cnf::new());
  assert_eq!(convert_to_cnf(0, 0, |_| SatOutput::ImpossibleInputs), vec![vec![]]);
  // A constant.
  assert_eq!(
    convert_to_cnf(0, 3, |_| SatOutput::Bits(vec![true, false, true])),
    vec![vec![1], vec![-2], vec![3]]
  );
}
