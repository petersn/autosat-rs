use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};

use sha2::{Digest, Sha256};

use crate::{allowed_settings, cnf_from_allowed, Cnf, SatLiteral, SatOutput};

/// Like `convert_to_cnf`, but caches results in `.autosat_cache/`.
pub fn convert_to_cnf_cached(
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Cnf {
  convert_to_cnf_cached_in(".autosat_cache", num_inputs, num_outputs, f)
}

/// Like `convert_to_cnf`, but caches results in `cache_dir`, one DIMACS file per
/// function. Cache errors are ignored, and it's safe to share between processes.
pub fn convert_to_cnf_cached_in(
  cache_dir: impl AsRef<Path>,
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Cnf {
  let n = num_inputs + num_outputs;
  let allowed = allowed_settings(num_inputs, num_outputs, f);
  let mut hasher = Sha256::new();
  hasher.update(format!("autosat-v1 {} {}\n", num_inputs, num_outputs));
  hasher.update(allowed.iter().flat_map(|w| w.to_le_bytes()).collect::<Vec<u8>>());
  let hash: String = hasher.finalize().iter().map(|b| format!("{:02x}", b)).collect();

  let dir = cache_dir.as_ref();
  let path = dir.join(format!("{}.cnf", hash));
  if let Some(cnf) = std::fs::read_to_string(&path).ok().and_then(|s| parse_dimacs(&s, n)) {
    return cnf;
  }
  let cnf = cnf_from_allowed(n, &allowed);
  let _ = write_atomically(dir, &path, &to_dimacs(&cnf, n));
  cnf
}

fn to_dimacs(cnf: &Cnf, n: usize) -> String {
  let mut s = format!("p cnf {} {}\n", n, cnf.len());
  for clause in cnf {
    for literal in clause {
      s += &format!("{} ", literal);
    }
    s += "0\n";
  }
  s
}

// Returns None for anything malformed or truncated.
fn parse_dimacs(s: &str, n: usize) -> Option<Cnf> {
  let mut lines = s.lines();
  let header: Vec<&str> = lines.next()?.split_whitespace().collect();
  if header.len() != 4 || header[..2] != ["p", "cnf"] || header[2].parse::<usize>().ok()? != n {
    return None;
  }
  let count: usize = header[3].parse().ok()?;
  let mut cnf = Cnf::with_capacity(count);
  for line in lines {
    let mut clause: Vec<SatLiteral> =
      line.split_whitespace().map(|t| t.parse().ok()).collect::<Option<_>>()?;
    if clause.pop()? != 0 || clause.iter().any(|&l| l == 0 || l.unsigned_abs() as usize > n) {
      return None;
    }
    cnf.push(clause);
  }
  (cnf.len() == count).then_some(cnf)
}

// Readers never see a partial file, since rename is atomic.
fn write_atomically(dir: &Path, path: &Path, contents: &str) -> std::io::Result<()> {
  static COUNTER: AtomicUsize = AtomicUsize::new(0);
  std::fs::create_dir_all(dir)?;
  let nanos = std::time::SystemTime::now()
    .duration_since(std::time::UNIX_EPOCH)
    .map_or(0, |d| d.subsec_nanos());
  let temp = dir.join(format!(
    ".tmp-{}-{}-{}",
    std::process::id(),
    COUNTER.fetch_add(1, Ordering::Relaxed),
    nanos
  ));
  std::fs::write(&temp, contents)?;
  std::fs::rename(&temp, path).or_else(|e| {
    let _ = std::fs::remove_file(&temp);
    Err(e)
  })
}
