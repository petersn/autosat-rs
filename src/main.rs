
fn main() {
  let and_gate = autosat::convert_to_cnf(
    2, 1, |input| autosat::SatOutput::Bits(vec![input[0] && input[1]]),
  );
  println!("and gate -> {:?}", and_gate);

  let and_gate = autosat::convert_to_cnf(
    2, 1, |input| autosat::SatOutput::Bits(vec![input[0] ^ input[1]]),
  );
  println!("xor gate -> {:?}", and_gate);
}
