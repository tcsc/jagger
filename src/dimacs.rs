use std::old_io;
use std::num::{self, SignedInt};
use std::str::FromStr;
use solver::{Expression, Term};
use solver::Term::{Lit, Not};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

pub struct Problem {
    pub varcount: usize,
    pub expression: Expression
}

impl Problem {
    pub fn new(varcount: usize, clauses: &[&[Term]]) -> Problem {
        Problem {
            varcount: varcount,
            expression: Expression::from(clauses)
        }
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
pub enum DimacsError {
    IoFailure (old_io::IoError),
    ParseFailure (String)
}

fn parse_failure<T>(s: String) -> Result<T, DimacsError> {
    Err(DimacsError::ParseFailure(s))
}

fn io_failure<T>(err: old_io::IoError) -> Result<T, DimacsError> {
    Err(DimacsError::IoFailure(err))
}

/**
 * Reads a signed integer from the supplied string.
 */
fn read_int(s: &str) -> Result<isize, DimacsError> {
    match FromStr::from_str(s) {
        Ok(n) => Ok(n),
        Err(_) => {
            parse_failure(format!("Not an integer: \"{}\"", s))
        }
    }
}

fn read_clause(s: &str) -> Result<Vec<Term>, DimacsError> {
    let mut clause = Vec::new();
    for item in s.trim().split(' ') {
        if item.is_empty() { continue; }
        match try!(read_int(item)) {
            n if n > 0 => clause.push(Lit(n as usize)),
            n if n < 0 => clause.push(Not(n.abs() as usize)),
            n => { break; }
        };
    }
    Ok(clause)
}

fn read_problem_header(s: &str) -> Result<(isize, isize), DimacsError> {
    let parts : Vec<&str> = s.split(' ').collect();
    match parts.len() {
        4 => {
            if parts[1] != "cnf" {
                return parse_failure(format!("expected \"cnf\", got \"{:?}\"", parts.get(1)))
            }
            let vars = try!(read_int(parts[2]));
            let clauses = try!(read_int(parts[3]));
            Ok((vars, clauses))
        }
        _ => {
            parse_failure(format!("Malformed header: {:?}", s))
        }
    }
}

#[test]
fn reading_problem_header_returns_counts() {
    assert!(read_problem_header("p cnf 42 128").unwrap() == (42, 128));
}

#[test]
fn problem_header_with_bad_type_returns_error() {
    match read_problem_header("p wtf 42 128") {
        Err(DimacsError::ParseFailure(_)) => {},
        _ => panic!("Expected parsing to fail")
    }
}

#[test]
fn problem_header_with_bad_varcount_returns_error() {
    match read_problem_header("p cnf narf 128") {
        Err(DimacsError::ParseFailure(_)) => {},
        _ => panic!("Expected parsing to fail")
    }
}

#[test]
fn problem_header_with_bad_clause_count_returns_error() {
    match read_problem_header("p cnf 42 zort") {
        Err (DimacsError::ParseFailure(_)) => {},
        _ => panic!("Expected parsing to fail")
    }
}

pub fn read<B: old_io::Buffer>(buf: &mut B) -> Result<Problem, DimacsError> {
    let mut clauses : Vec<Vec<Term>> = Vec::new();
    let mut nvars = 0;
    for line in buf.lines() {
        match line {
            Ok(s) => {
                let line = s.as_slice().trim();
                match line.chars().next() {
                    None => {  /* empty line */ },
                    Some(c) if c == 'c' => { /* comment */ },
                    Some(c) if c == 'p' => {
                        let (v, _)= try!(read_problem_header(line));
                        nvars = v;
                    }
                    Some(_) => {
                        clauses.push(try!(read_clause(line)));
                    }
                }
            },
            Err(err) => return io_failure(err)
        }
    }

    let slices : Vec<&[Term]> = clauses.iter()
                                       .map(|v| &v[])
                                       .collect();
    Ok(Problem::new(nvars as usize, &slices[]))
}

#[cfg(test)]
fn make_buffer(lines: &[&str]) -> old_io::MemReader {
    let mut text = old_io::MemWriter::new();
    for s in lines.iter() {
        match text.write_str(*s) {
            n => {}
        }
    }
    old_io::MemReader::new( text.into_inner() )
}

#[test]
fn dimacs_reader() {
    let mut reader = make_buffer(&[
        "\n",
        "c\n",
        "c comment\n",
        "c\n",
        "p cnf 5 3\n",
        "1   -5 4 0\n",
        "-1 5 3 4 0\n",
        "-3 -4 0"
    ]);

    let problem = read(&mut reader).unwrap();
    assert!(problem.varcount == 5, "Expected varcount 5, got {:?}", problem.varcount);

    assert!(problem.expression.clauses().count() == 3);
    let mut iter = problem.expression.clauses();
    let c1 = iter.next().unwrap();
    assert!(c1.terms() == [Lit(1), Not(5), Lit(4)], "Expected [1, ~5, 4], got {:?}", c1);

    let c2 = iter.next().unwrap();
    assert!(c2.terms() == [Not(1), Lit(5), Lit(3), Lit(4)],
        "Expected [~1, 5, 3, 4], got {:?}", c2);

    let c3 = iter.next().unwrap();
    assert!(c3.terms() == [Not(3), Not(4)],
        "Expected [~3, ~4], got {:?}", c3);

    assert!(iter.next() == None);

}