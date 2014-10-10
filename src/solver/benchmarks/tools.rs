use std::io;

#[config(test)]
pub fn load_problem(s: &str) -> ::dimacs::Problem {
    let mut text = io::MemWriter::new();
    text.write_str(s);
    let mut reader = io::MemReader::new( text.unwrap() );
    ::dimacs::read(&mut reader).unwrap()
}
