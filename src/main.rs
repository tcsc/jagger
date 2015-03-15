#![feature(box_syntax)]
#![allow(unstable)]
#![allow(dead_code)]
#![feature(io)]
#![feature(test)]

#[macro_use] extern crate log;
extern crate getopts;
extern crate graphviz;
extern crate test;
extern crate time;

mod collections;
mod metadata;
mod pkg;
mod solver;
mod dimacs;
mod formulator;

use getopts::Options;
use std::io::BufReader;
use std::path::PathBuf;

fn init_opts() -> Options {
	let mut opts = Options::new();
	opts.reqopt("f", "file", "The file to load", "FILE");
	opts
}

struct Args {
	file: PathBuf
}

impl Args {
    fn new() -> Args {
        Args { file: PathBuf::new("") }
    }
}

fn parse_args(argv: &[String]) -> Option<Args> {
    let opts = init_opts();
    let m = match opts.parse(argv.tail()) {
        Ok(m) => { m },
        Err(f) => { return None }
    };

    let f = PathBuf::new(&m.opt_str("f").unwrap()[..]);
    let result = Args {
        file: f
    };
    Some(result)
}

#[test]
fn arg_parser_reads_input_file() {
    let argv : Vec<String> = ["binary", "--file", "some/file"]
                                .iter()
                                .map(|s| s.to_string())
                                .collect();
    let opts = parse_args(&argv[..]).unwrap();
    assert_eq!(PathBuf::new("some/file"), opts.file);
}

#[cfg(not(test))]
fn main() {
	use std::fs::File;

	use dimacs::read as read_dimacs;
	use solver::{Solution, solve};

	let args : Vec<String> = std::env::args().collect();
	let opts = parse_args(&args[..]).unwrap();
	let file = match File::open(&opts.file) {
		Ok(f) => f,
		Err(reason) => panic!("file open failed: {}", reason.description())
	};

	let problem = match read_dimacs(&mut BufReader::new(file)) {
		Ok(p) => p,
		Err(reason) => panic!("file parising failed: {:?}", reason)
	};

	let start_time = time::precise_time_ns();

	match solve(&problem.expression, problem.varcount, Solution::new(problem.varcount)) {
		Some(_) => println!("SAT"),
		None => println!("UNSAT"),
	};

	let elapsed_time = time::precise_time_ns() - start_time;
	println!("Took {} s", (elapsed_time as f64) / 1e+9);
}
