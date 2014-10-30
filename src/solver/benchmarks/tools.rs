use std::io;

#[config(test)]
pub fn load_problem(s: &str) -> ::dimacs::Problem {
    let mut text = io::MemWriter::new();
    match text.write_str(s) {
    	Ok(_) => {},
    	Err(e) => { fail!("write failed: {}", e); }
    }
    let mut reader = io::MemReader::new( text.unwrap() );
    ::dimacs::read(&mut reader).unwrap()
}
