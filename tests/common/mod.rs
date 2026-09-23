#![allow(dead_code)]

pub mod cases;
pub mod reference;

use autosat::Cnf;

/// FNV-1a over the literals, with clause separators.
pub fn fingerprint(cnf: &Cnf) -> u64 {
  let mut hash = 0xcbf29ce484222325u64;
  for clause in cnf {
    for &literal in clause.iter().chain(std::iter::once(&0)) {
      for byte in literal.to_le_bytes() {
        hash = (hash ^ byte as u64).wrapping_mul(0x100000001b3);
      }
    }
  }
  hash
}
