use std::collections::{TrieMap};
use std::fmt;
use std::ops;
use std::rc::Rc;
use std::slice;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
pub type Var = uint;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(PartialEq, Eq, Show, Clone)]
pub enum SolutionValue { Unassigned, True, False }

impl SolutionValue {
    fn from_bool(val: bool) -> SolutionValue {
        match val {
            true => True,
            false => False
        }
    }

    fn as_bool(&self) -> bool {
        match *self {
            Unassigned => fail!("Expected True or False"),
            True => true,
            False => false
        }
    }
}

/**
 * Slightly odd bitwise OR semantics that are set up to make it easier to 
 * analayse a collecton of terms by ORing their values together. The 
 * resulting truth table looks something like
 *
 *  OR         | True | False      | Unassigned
    ===========================================
 *  True       | True | True       | True
 *  False      | True | False      | Unassigned
 *  Unassigned | True | Unassigned | Unassigned
 */
impl BitOr<SolutionValue, SolutionValue> for SolutionValue {
    fn bitor(&self, rhs: &SolutionValue) -> SolutionValue {
        if *self == True || *rhs == True { 
            True
        }
        else if *self == Unassigned || *rhs == Unassigned {
            Unassigned
        }
        else {
            False
        }
    }
}

#[test]
fn unassigned_solution_value_propagates_through_or() {
    assert!((Unassigned | True) == True, "Expected True, got {}", Unassigned | True);
    assert!((Unassigned | False) == Unassigned);
    assert!((True | Unassigned) == True);
    assert!((False | Unassigned) == Unassigned);
}

#[test]
fn oring_assigned_solution_values_behaves_like_boolean() {
    assert!((True | True) == True);
    assert!((True | False) == True);
    assert!((False | True) == True);
    assert!((False | False) == False);
}

impl ops::Not<SolutionValue> for SolutionValue {
    fn not(&self) -> SolutionValue {
        match *self {
            Unassigned => Unassigned,
            True => False,
            False => True
        }
    }
}

#[test]
fn not_unassigned_solution_value_is_unassigned() {
    assert!(!Unassigned == Unassigned)
}

#[test]
fn not_assigned_solution_behaves_like_boolean() {
    assert!(!True == False);
    assert!(!False == True);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------


/**
 * A variable-to-value mapping. Implemented as a thumping great vector, as
 * every variable will have to have a value at some point anyway, and a vector
 * will be more memory & time efficient than a tree map. The tradeoff is that
 * while we will use less peak memory, we will use a smaller chunk for longer.
 * 
 * Note that the sollution could be further compressed by storing the values as
 * two-bit (e.g.: unassigned: 00, true: 01, false: 10) values packed into
 * larger cells. We'd need to actually benchmark this to see if the memory & 
 * cache efficiency is worth the extra pack & unpack code.
 */
#[deriving(PartialEq, Clone)]
pub struct Solution {
    values: Vec<SolutionValue>
}

impl<'a> Solution {
    /**
     * Creates an empty solution
     */
    pub fn new(n: uint) -> Solution { 
        Solution { values: Vec::from_elem(n+1, Unassigned) }
    }

    /**
     * Creates a solution from predefined values encoded as a (variable, value) pair
     */
    pub fn from(varcount: uint, values: &[(Var, SolutionValue)]) -> Solution {
        let mut s = Solution::new(varcount);
        for &(var, val) in values.iter() {
            s.set(var, val)
        }
        s
    }

    /**
     * Sets a value in the solution
     */
    pub fn set(&mut self, var: Var, val: SolutionValue) {
        *self.values.get_mut(var) = val;
    }

    pub fn unset(&mut self, var: Var) {
        *self.values.get_mut(var) = Unassigned;
    }

    /**
     * Resets all variables in the supplied iterator to Unassigned.
     */
    pub fn unset_all<I:Iterator<Var>>(&mut self, mut iter: I) {
        for var in iter {
            self.set(var, Unassigned)
        }
    }

    /**
     * Fetches a value in the solution
     */
    pub fn get(&self, var: Var) -> SolutionValue {
        self.values[var]
    }

    pub fn assigned_vars(&self) -> Vec<Var> {
        self.values.iter()
                   .enumerate()
                   .filter(|&(_, v)| *v != Unassigned)
                   .map(|(k, _)| k)
                   .collect()
    }

    pub fn is_assigned(&self, v: Var) -> bool {
        self.get(v) != Unassigned
    }
}

impl fmt::Show for Solution {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
  
        try!(write!(f, "["));
        for (k, v) in self.values.iter().enumerate() {
            if *v == Unassigned {
                continue;
            }

            if first  { first = false; } else { try!(write!(f, ", ")); }
            try!(write!(f, "{}: {}", k, v));
        }
        write!(f, "]")
    }
}

impl Index<Var, SolutionValue> for Solution {
    fn index<'a>(&'a self,  v: &Var) -> &'a SolutionValue {
        self.values.index(v)
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(Clone)]
pub enum Term { Lit(Var), Not(Var) }

impl Term {
    pub fn var(&self) -> uint {
        match *self {
            Lit(v) => v,
            Not(v) => v
        }
    }

    pub fn value(&self, s: &Solution) -> SolutionValue {
        match s.get(self.var()) {
            Unassigned => Unassigned,
            val => match *self { Lit (_) => val, Not (_) => !val }
        } 
    }
}

impl PartialEq for Term {
    fn eq(&self, other: &Term) -> bool {
        match *self {
            Lit(x) => match *other { Lit(y) => x == y, _ => false },
            Not(x) => match *other { Not(y) => x == y, _ => false }
        }
    }
}

impl Eq for Term {}

impl fmt::Show for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Lit(x) => write!(f, "{}", x),
            Not(x) => write!(f, "~{}", x)
        }
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

pub struct Clause(pub Vec<Term>); 

/**
 * Deprecated
 */
#[deriving(Clone)]
impl Clause {
    pub fn new() -> Clause {
        Clause(vec![])
    }

    pub fn from(terms: &[Term]) -> Clause {
        let mut r = Clause::new();
        for t in terms.iter() {
            r.add(*t)
        };
        r
    }

    pub fn add(&mut self, t: Term) {
        let Clause(ref mut r) = *self;
        r.push(t.clone())
    }

    pub fn terms<'a>(&'a self) -> slice::Items<'a, Term> {
        let Clause(ref r) = *self;
        r.iter()   
    }

    pub fn len(&self) -> uint {
        let Clause(ref r) = *self;
        r.len()
    }
}

impl FromIterator<Term> for Clause {
    fn from_iter<T: Iterator<Term>>(mut terms: T) -> Clause {
        let mut r = Clause::new();
        for t in terms {
            r.add(t.clone())
        }
        r
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        let Clause(ref me) = *self;
        let Clause(ref it) = *other;
        me == it
    }
}

impl fmt::Show for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Clause(ref terms) = *self;
        let mut first = true;
        try!(write!(f, "("));
        for ref t in terms.iter() {
            if !first { try!(write!(f, " | " )); } else { first =  false; }
            try!(t.fmt(f));
        }
        write!(f, ")")
    }
}

// ----------------------------------------------------------------------------
// 
// ----------------------------------------------------------------------------
pub type ClauseRef = Rc<Clause>;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * An expression consisting of multiple Clauses that are ANDed together.
 */
 #[deriving(Clone)]
pub struct Expression {
    data: Vec<Term>,
    offsets: Vec<(uint, uint)>,
    index: TrieMap<Vec<(uint, uint)>>
}

/**
 * An iterator type for iterating over clauses in an expression. Turns the 
 * internal representation of clauses (i.e. a collection of (offset, len) 
 * pairs) into slices for external consumption.
 */
struct ClauseIterator<'a> { 
    data: &'a Vec<Term>,
    offsets: slice::Items<'a, (uint, uint)>
}

impl<'a> Iterator<&'a[Term]> for ClauseIterator<'a> {
    fn next(&mut self) -> Option<&'a[Term]> {
        match self.offsets.next() {
            None => None,
            Some (&(offset, len)) => {
                Some(self.data.slice(offset, offset + len))
            }
        }
    }
}

impl Expression {
    pub fn new() -> Expression { 
        Expression {
            data: Vec::new(),
            offsets: Vec::new(),
            index: TrieMap::new()
        }
    }

    /**
     * Creates an expression from a set of collections of terms
     */
    pub fn from(clauses: &[&[Term]]) -> Expression {
        let mut exp = Expression::new();

        for clause in clauses.iter() {
            let slice = (exp.data.len(), clause.len());
            exp.offsets.push(slice);
            exp.data.push_all(*clause);

            for v in clause.iter().map(|t| t.var()) {
                if exp.index.contains_key(&v) {
                    exp.index.find_mut(&v).unwrap().push(slice)
                }
                else {
                    exp.index.insert(v, vec![slice]);
                }
            }
        }
        exp
    }

    pub fn clauses(&self) -> ClauseIterator {
        ClauseIterator { 
            data: &self.data, 
            offsets: self.offsets.iter() 
        }
    }

    pub fn clauses_containing(&self, v: Var) -> ClauseIterator {
        let iter = match self.index.find(&v) {
            Some(v) => v.iter(),
            None => [].iter()    
        };
        ClauseIterator {
            data: &self.data,
            offsets: iter
        }
    }

    /**
     * Attempts to apply the supplied solution to the expression to see if it
     * passes.
     */
    pub fn apply(&self, sln: &Solution) -> SolutionValue {
        for clause in self.clauses() {
            let mut val = False;
            for term in clause.iter() {
                val = val | term.value(sln);
            }
            match val {
                Unassigned | False => return val,
                _ => ()
            }
        }
        True
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        self.data == other.data && self.offsets == other.offsets
    }    
}

impl fmt::Show for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        try!(write!(f, "["));
        
        for c in self.clauses() {
            if !first { try!(write!(f, " & " )); } else { first = false; }
            try!(c.fmt(f));
        }
        write!(f, "]")
    }
}

#[test]
fn get_clauses_containing_var_returns_only_clauses_containing_var() {
    let sln = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(4)]
    ]);

    let clauses : Vec<&[Term]> = sln.clauses_containing(1).collect();
    assert!(clauses.len() == 2);
    assert!(clauses.iter().find(|c| **c == [Lit(1), Lit(2), Lit(3)].as_slice()).is_some())
    assert!(clauses.iter().find(|c| **c == [Lit(1)].as_slice()).is_some())
}

#[test]
fn get_clauses_containing_var_handles_empty_expression() {
    let sln = Expression::new();
    let clauses : Vec<&[Term]> = sln.clauses_containing(1).collect();

    assert!(clauses.len() == 0);
}

#[test]
fn get_clauses_containing_var_handles_empty_result() {
    let sln = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(4)]
    ]);
    let clauses : Vec<&[Term]> = sln.clauses_containing(5).collect();

    assert!(clauses.len() == 0);
}