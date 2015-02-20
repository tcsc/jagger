use std::old_io;

#[cfg(test)]
pub fn load_problem(s: &str) -> ::dimacs::Problem {
    let mut text = old_io::MemWriter::new();
    match text.write_str(s) {
    	Ok(_) => {},
    	Err(e) => { panic!("write failed: {}", e); }
    }
    let mut reader = old_io::MemReader::new( text.into_inner() );
    ::dimacs::read(&mut reader).unwrap()
}
