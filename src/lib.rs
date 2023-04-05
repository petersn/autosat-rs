pub type SatLiteral = i32;
pub type SatClause = Vec<SatLiteral>;
pub type Cnf = Vec<SatClause>;

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

#[inline(always)]
fn evaluate_clause(clause: &[SatLiteral], setting: u32) -> bool {
  for &literal in clause {
    let bit = (setting >> (literal.abs() as usize - 1)) & 1 == 1;
    if (literal > 0) == bit {
      return true;
    }
  }
  false
}

fn test_useful(
  clause: &[SatLiteral],
  settings_to_rule_out: &[u32],
) -> bool {
  // Make sure that at least one setting is ruled out.
  for &setting_to_rule_out in settings_to_rule_out {
    if !evaluate_clause(clause, setting_to_rule_out) {
      return true;
    }
  }
  false
}

fn test_feasible(
  clause: &[SatLiteral],
  allowed_behavior_lookup: &[bool],
  max_setting: u32,
) -> bool {
  // Make sure no allowed behavior is ruled out.
  for setting in 0..max_setting {
    if allowed_behavior_lookup[setting as usize] && !evaluate_clause(clause, setting) {
      return false;
    }
  }
  true
}

fn test_feasible_and_useful(
  max_setting: u32,
  clause: &[SatLiteral],
  allowed_behavior_lookup: &[bool],
  settings_to_rule_out: &[u32],
) -> bool {
  test_feasible(clause, allowed_behavior_lookup, max_setting)
    && test_useful(clause, settings_to_rule_out)
}

pub fn convert_to_cnf(
  num_inputs: usize,
  num_outputs: usize,
  f: impl Fn(&[bool]) -> SatOutput,
) -> Cnf {
  let bit_count = num_inputs + num_outputs;
  println!("Bit count: {}", bit_count);

  let max_setting = 2u32.pow(bit_count as u32);

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

  let mut positive_clauses_by_length: Vec<Vec<SatClause>> = (0..=bit_count)
    .map(|_| Vec::new())
    .collect();
  for clause_index in 0..2usize.pow(bit_count as u32) {
    let mut clause = Vec::new();
    for bit_index in 0..bit_count {
      if (clause_index >> bit_index) & 1 == 1 {
        clause.push(bit_index as SatLiteral + 1);
      }
    }
    positive_clauses_by_length[clause.len()].push(clause);
  }

  fn fill_with_ones(bits: &mut Vec<u64>, count: usize) {
    let words = (count + 63) / 64;
    bits.resize(words, 0);
    // Fill every word with ones.
    for i in 0..words {
      bits[i] = u64::MAX;
    }
    // Clear the extra bits.
    for i in count..64 * words {
      clear_bit(bits, i);
    }
  }

  let mut settings_to_rule_out: Vec<u32> = (0..2u32.pow(bit_count as u32))
    .filter(|&i| !allowed_behavior_lookup[i as usize])
    .collect();
  let mut behavior_to_remove = vec![];
  fill_with_ones(&mut behavior_to_remove, settings_to_rule_out.len());

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

  let mut cnf = Cnf::new();

  for current_max_length in 1.. {
    let remaining_weight = behavior_to_remove.iter().map(|&x| x.count_ones()).sum::<u32>();
    if remaining_weight == 0 {
      println!("  Found all {} clauses!", cnf.len());
      break;
    }
    let polarities = 2usize.pow(current_max_length as u32);

    // Filter down settings_to_rule_out and behavior_to_remove.
    println!("  Settings to rule out: {:?}", settings_to_rule_out);
    println!("  Behavior to remove: {:?}", behavior_to_remove);
    settings_to_rule_out = settings_to_rule_out
      .into_iter()
      .enumerate()
      .filter_map(|(i, setting)| {
        match get_bit(&behavior_to_remove, i) {
          true => Some(setting),
          false => None,
        }
      })
      .collect();
    fill_with_ones(&mut behavior_to_remove, settings_to_rule_out.len());
    println!("  POST Settings to rule out: {}", settings_to_rule_out.len());
    println!(
      "  Clauses so far: {} - Current max length: {} -- Remaining weight: {}",
      cnf.len(), current_max_length, remaining_weight,
    );

    println!(
      "      Filtering down from {} clauses by {} polarities.",
      positive_clauses_by_length[current_max_length].len(),
      polarities
    );
    println!("      Clauses: {:?}", positive_clauses_by_length[current_max_length]);

    let mut feasible_useful_clauses_of_this_length: Vec<SatClause> = Vec::new();
    let mut current_clause = vec![0; current_max_length];
    for clause in &positive_clauses_by_length[current_max_length] {
      for polarity_setting in 0..polarities {
        for i in 0..current_max_length {
          current_clause[i] = match polarity_setting & (1 << i) == 0 {
            true => -clause[i],
            false => clause[i],
          };
        }
        let feasible = test_feasible(
          &current_clause, &allowed_behavior_lookup, max_setting
        );
        let useful = test_useful(
          &current_clause, &settings_to_rule_out
        );
        println!("      Testing clause: {:?}, feasible = {}, useful = {}", current_clause, feasible, useful);
        if test_feasible_and_useful(
          max_setting, &current_clause, &allowed_behavior_lookup, &settings_to_rule_out
        ) {
          println!("      Clause is feasible and useful: {:?}", current_clause);
          feasible_useful_clauses_of_this_length.push(current_clause.clone());
        }
      }
    }

    if feasible_useful_clauses_of_this_length.is_empty() {
      println!("No feasible useful clauses of length {}", current_max_length);
      continue;
    }

    let mut matrix = vec![0; feasible_useful_clauses_of_this_length.len() * behavior_to_remove.len()];
    macro_rules! get_row {
      ($row:expr) => {{
        let row = $row;
        &mut matrix[row * behavior_to_remove.len()..(row + 1) * behavior_to_remove.len()]
      }};
    }

    // Fill in the matrix.
    for (row_idx, clause) in feasible_useful_clauses_of_this_length.iter().enumerate() {
      let row = get_row!(row_idx);
      for (col_idx, &setting) in settings_to_rule_out.iter().enumerate() {
        println!("  mat[{}, {}] = evaluate_clause({:?}, {}) = {}", row_idx, col_idx, clause, setting, evaluate_clause(&clause, setting));
        if !evaluate_clause(&clause, setting) {
          set_bit(row, col_idx);
        }
      }
    }

    loop {
      // Find the row with the greatest overlap with behavior_to_remove.
      let mut highest_pop_count = 0;
      let mut highest_pop_count_row_idx = 0;
      for row_idx in 0..feasible_useful_clauses_of_this_length.len() {
        let row = get_row!(row_idx);
        let mut pop_count = 0;
        for (i, &word) in row.iter().enumerate() {
          pop_count += (word & behavior_to_remove[i]).count_ones();
        }
        if pop_count > highest_pop_count {
          highest_pop_count = pop_count;
          highest_pop_count_row_idx = row_idx;
        }
      }
      if highest_pop_count == 0 {
        break;
      }

      // Mark behaviors as ruled out.
      cnf.push(feasible_useful_clauses_of_this_length[highest_pop_count_row_idx].clone());
      let highest_pop_count_row = get_row!(highest_pop_count_row_idx);
      let mut any = 0;
      for i in 0..behavior_to_remove.len() {
        let new_value = behavior_to_remove[i] & !highest_pop_count_row[i];
        behavior_to_remove[i] = new_value;
        any |= new_value;
      }
      if any == 0 {
        break;
      }
      // Print the remaining pop-count.
      println!(
        "      Remaining pop-count: {}",
        behavior_to_remove.iter().map(|&x| x.count_ones()).sum::<u32>()
      );
    }
  }

  cnf
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn it_works() {
    let and_gate = convert_to_cnf(2, 1, |input| SatOutput::Bits(vec![input[0] && input[1]]));
    println!("{:?}", and_gate);
  }
}
