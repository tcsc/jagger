use std::vec;

#[cfg(test)]
pub fn load_problem(s: &str) -> ::dimacs::Problem {
    let mut text : Vec<u8> = Vec::new();
    match text.write(s.as_bytes()) {
    	Ok(_) => {},
    	Err(e) => { panic!("write failed: {}", e); }
    }
    ::dimacs::read(&text[..]).unwrap()
}
