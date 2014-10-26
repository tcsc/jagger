use std::collections::{TreeMap, TrieSet};
use std::collections::treemap::{Entries};
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

impl BitOr<SolutionValue, SolutionValue> for SolutionValue {
    fn bitor(&self, rhs: &SolutionValue) -> SolutionValue {
        if (*self == Unassigned) || (*rhs == Unassigned) {
            Unassigned
        }
        else {
            if self.as_bool() | rhs.as_bool() {
               True 
            }
            else {
                False
            }
        }
    }
}

#[test]
fn unassigned_solution_value_propagates_through_or() {
    assert!((Unassigned | True) == Unassigned);
    assert!((Unassigned | False) == Unassigned);
    assert!((True | Unassigned) == Unassigned);
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
 * A variable-to-value mapping.
 * 
 * This might be made faster & more memory-efficient by implementing it as an array 
 * rather than a tree, especially given that every variable in the problem will 
 * definitely  have a value by the end of the solve.
 *
 * It could be further compressed by storing the values as two-bit (ie: 
 * unassigned: 00, true: 01, false: 10) values packed into larger cells. We'd need to
 * actually benchmark this to see if the memory & cache efficiency is worth the extra 
 * pack & unpack code.
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

//    pub fn iter(&'a self) -> Entries<'a, Var, bool> {
//        let Solution(ref map) = *self;
//        map.iter()
//    }
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

pub type ClauseRef = Rc<Clause>;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * An expression consisting of multiple Clauses that are ANDed together. The 
 * clauses are reference counted so that they can appear in multiple iterations
 * of the expression as it gets progressively simplified during solving. 
 *
 * This structure is pretty inefficient, with both reference counting and 
 * indirection all over the place. A more efficient implemetation might store 
 * the master expression as a giant array with all the clauses packed together 
 * and referenced by slices during the actual solve.
 *
 * Get some benchmarking in first to see if its worth it, though. 
 */
 #[deriving(Clone)]
pub struct Expression(Vec<ClauseRef>);

impl Expression {
    pub fn new() -> Expression { Expression(vec![]) }

    pub fn from(clauses: &[&[Term]]) -> Expression {
        let mut e = Expression::new();
        for r in clauses.iter() {
            e.add( Clause::from(*r) );
        }
        e
    }

    pub fn iter<'a>(&'a self) -> slice::Items<'a, Rc<Clause>> //-> Items<Rc<Clause>> 
    {
        let Expression(ref v) = *self;
        v.iter()
    }

    fn len(&self) -> uint {
        let Expression(ref v) = *self;
        v.len()
    }

    fn add(&mut self, clause: Clause) {
        let Expression(ref mut v) = *self;
        v.push(Rc::new(clause));
    }

    pub fn add_ref(&mut self, clause: &Rc<Clause>) {
        let Expression(ref mut v) = *self;
        v.push(clause.clone())
    }

    pub fn is_empty(&self) -> bool {
        let Expression(ref v) = *self;
        v.is_empty()    
    }

    /**
     * Attempts to apply the supplied solution to the expression to see if it
     * passes.
     */
    pub fn apply(&self, sln: &Solution) -> SolutionValue {
        for clause in self.iter() {
            let mut val = False;
            for term in clause.terms() {
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
        let Expression(ref me) = *self;
        let Expression(ref it) = *other;
        me == it
    }    
}

impl fmt::Show for Expression {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let Expression(ref clauses) = *self;
        let mut first = true;
        try!(write!(f, "["));
        for ref r in clauses.iter() {
            if !first { try!(write!(f, " & " )); } else { first = false; }
            try!(r.fmt(f));
        }
        write!(f, "]")
    }
}