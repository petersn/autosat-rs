
fn main() {
  let and_gate = autosat::convert_to_cnf(
    2, 1, |input| autosat::SatOutput::Bits(vec![input[0] && input[1]]),
  );
  println!("and gate -> {:?}", and_gate);

  let f = autosat::convert_to_cnf(
    10, 1, |input| {
      // if input[1] && !input[2] {
      //   autosat::SatOutput::DontCare
      // } else if input[2] && !input[0] {
      //   autosat::SatOutput::ImpossibleInputs
      // } else if input[0] {
      //   autosat::SatOutput::Bits(vec![input[1], input[2]])
      // } else {
      //   autosat::SatOutput::Bits(vec![input[1] || input[2], input[1] && input[2]])
      // }
      // Xor all of the bits together.
      let mut result = false;
      for &bit in input {
        result ^= bit;
      }
      autosat::SatOutput::Bits(vec![result])
    },
  );

  println!("xor gate -> {:?}", f);
}
