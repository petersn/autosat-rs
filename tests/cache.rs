mod common;

use std::path::PathBuf;

use autosat::{convert_to_cnf, convert_to_cnf_cached_in, SatOutput};
use common::cases::{aes_sbox, random, xor, Case};

fn temp_dir(name: &str) -> PathBuf {
  let dir = std::env::temp_dir().join(format!("autosat-test-{}-{}", name, std::process::id()));
  let _ = std::fs::remove_dir_all(&dir);
  dir
}

fn cache_files(dir: &PathBuf) -> Vec<PathBuf> {
  std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).collect()
}

fn cached(dir: &PathBuf, case: &Case) -> autosat::Cnf {
  convert_to_cnf_cached_in(dir, case.num_inputs, case.num_outputs, &case.f)
}

#[test]
fn cache_round_trips() {
  let dir = temp_dir("round-trip");
  let cases = [xor(5), aes_sbox(), random(4, 3, 20, 20, 1), random(3, 0, 0, 50, 2)];
  for case in &cases {
    let expected = convert_to_cnf(case.num_inputs, case.num_outputs, &case.f);
    assert_eq!(cached(&dir, case), expected);
    assert_eq!(cached(&dir, case), expected);
  }
  assert_eq!(cache_files(&dir).len(), cases.len());
  // Degenerate CNFs: empty, and a single empty clause.
  for (f, expected) in [(SatOutput::DontCare, vec![]), (SatOutput::ImpossibleInputs, vec![vec![]])] {
    for _ in 0..2 {
      assert_eq!(convert_to_cnf_cached_in(&dir, 0, 0, |_| f.clone()), expected);
    }
  }
  let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn bad_cache_files_are_ignored() {
  let dir = temp_dir("bad-files");
  let case = aes_sbox();
  let expected = cached(&dir, &case);
  let path = cache_files(&dir).pop().unwrap();
  let good = std::fs::read_to_string(&path).unwrap();
  let truncated_line = &good[..good.len() - 3];
  let dropped_line = &good[..good[..good.len() - 1].rfind('\n').unwrap() + 1];
  for bad in ["", "garbage", "p cnf 16 1\n1 2 x 0\n", truncated_line, dropped_line] {
    std::fs::write(&path, bad).unwrap();
    assert_eq!(cached(&dir, &case), expected);
    assert_eq!(std::fs::read_to_string(&path).unwrap(), good);
  }
  let _ = std::fs::remove_dir_all(&dir);
}

#[test]
fn concurrent_use_is_safe() {
  let dir = temp_dir("concurrent");
  let cases: Vec<Case> = (0..4).map(|seed| random(6, 5, 0, 0, seed)).collect();
  let expected: Vec<_> =
    cases.iter().map(|c| convert_to_cnf(c.num_inputs, c.num_outputs, &c.f)).collect();
  std::thread::scope(|scope| {
    for t in 0..16 {
      let (dir, cases, expected) = (&dir, &cases, &expected);
      scope.spawn(move || {
        for i in 0..20 {
          let k = (t + i) % cases.len();
          assert_eq!(cached(dir, &cases[k]), expected[k]);
        }
      });
    }
  });
  assert_eq!(cache_files(&dir).len(), cases.len());
  let _ = std::fs::remove_dir_all(&dir);
}
