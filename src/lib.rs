pub type SatLiteral = i32;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Cnf {
  clauses: Vec<Vec<SatLiteral>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum SatOutput {
  Bits(Vec<bool>),
  DontCare,
  ImpossibleInputs,
}

fn bits_to_num(bits: &[bool]) -> usize {
  let mut result = 0;
  for i in 0..bits.len() {
    result += (bits[i] as usize) << i;
  }
  result
}

#[inline(always)]
fn set_bit(bits: &mut [u64], index: usize) {
  bits[index / 64] |= 1 << (index % 64);
}

#[inline(always)]
fn clear_bit(bits: &mut [u64], index: usize) {
  bits[index / 64] &= !(1 << (index % 64));
}

#[inline(always)]
fn get_bit(bits: &[u64], index: usize) -> bool {
  (bits[index / 64] >> (index % 64)) & 1 == 1
}

pub fn convert_to_cnf(
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Cnf {
  let bit_count = num_inputs + num_outputs;
  // Construct a lookup table of allowed behaviors.
  let mut allowed_behavior_lookup = vec![false; 2usize.pow(bit_count as u32)];
  for i in 0..2usize.pow(num_inputs as u32) {
    let input: Vec<bool> = (0..num_inputs).map(|j| (i >> j) & 1 == 1).collect();
    let output = f(&input);
    let base_index = i << num_outputs;
    match output {
      SatOutput::Bits(bits) => {
        allowed_behavior_lookup[base_index + bits_to_num(&bits)] = true;
      }
      SatOutput::DontCare => {
        for j in 0..2usize.pow(num_outputs as u32) {
          allowed_behavior_lookup[base_index + j] = true;
        }
      }
      SatOutput::ImpossibleInputs => {}
    }
  }
  println!(
    "Behavior lookup table of size: {}",
    allowed_behavior_lookup.len()
  );

  let mut settings_to_rule_out: Vec<u32> = (0..2u32.pow(bit_count as u32))
    .filter(|&i| !allowed_behavior_lookup[i as usize])
    .collect();
  let mut row_width = (settings_to_rule_out.len() + 63) / 64;
  let mut behavior_to_remove = vec![0u64; row_width];
  for i in 0..settings_to_rule_out.len() {
    set_bit(&mut behavior_to_remove, i);
  }

  // // Find all clauses that don't rule out any allowed behavior ("feasible" clauses).
  // let mut feasible_clauses: Vec<Vec<SatLiteral>> = Vec::new();
  // 'clause_loop: for mut clause_index in 0..3usize.pow(bit_count as u32) {
  //   let mut clause = Vec::new();
  //   for bit_index in 0..bit_count {
  //     match clause_index % 3 {
  //       0 => clause.push(-(bit_index as SatLiteral + 1)),
  //       1 => clause.push(bit_index as SatLiteral + 1),
  //       2 => {}
  //       _ => unreachable!(),
  //     }
  //     clause_index /= 3;
  //   }

  //   // Check if this clause rules out any allowed behavior.
  //   'allowed_loop: for (i, allowed) in allowed_behavior_lookup.iter().enumerate() {
  //     if *allowed {
  //       // Make sure at least one literal in the clause is satisfied.
  //       for &literal in &clause {
  //         let bit = (i >> (literal.abs() as usize - 1)) & 1 == 1;
  //         if (literal > 0) == bit {
  //           continue 'allowed_loop;
  //         }
  //       }
  //       // If we get here, the clause rules out this allowed behavior.
  //       continue 'clause_loop;
  //     }
  //   }

  //   feasible_clauses.push(clause);
  // }
  // println!("Found {} feasible clauses", feasible_clauses.len());

  let mut current_max_length = 0;
  while behavior_to_remove.iter().map(|&x| x.count_ones()).sum::<u32>() != 0 {
    current_max_length += 1;
    
  }

  todo!()
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    let and_gate = convert_to_cnf(2, 1, |input| SatOutput::Bits(vec![input[0] && input[1]]), 5);
    println!("{:?}", and_gate);
  }
}
