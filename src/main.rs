/*fn main() -> Result<(), CompileError> {
  let mut args = std::env::args();
  let file_name = args
    .nth(1)
    .expect("Expected file name as argument on command line");

  let content = std::fs::read_to_string(file_name)?;
  let bytes = compile(&content)?;

  todo!();
}*/
fn main() {
  println!("Hello, world!");
}
