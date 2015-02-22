use std::fmt;
use std::ops;
use std::cmp;
use std::slice;
use std::iter::{FromIterator, IntoIterator, repeat};
use std::collections;
use std::collections::{BTreeSet, VecMap};

use self::SolutionValue::{True, False, Unassigned, Conflict};
use self::Term::{Lit, Not};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
pub type Var = usize;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct VarSet(BTreeSet<Var>);

impl VarSet {
    pub fn new () -> VarSet { VarSet(BTreeSet::new()) }

    pub fn insert(&mut self, value: Var) {
        let VarSet(ref mut this) = *self;
        this.insert(value);
    }

    pub fn remove(&mut self, value: &Var) -> bool {
        let VarSet(ref mut this) = *self;
        this.remove(value)
    }

    pub fn contains(&mut self, value: &Var) -> bool {
        let VarSet(ref mut this) = *self;
        this.contains(value)
    }

    pub fn iter(&self) -> collections::btree_set::Iter<Var> {
        let VarSet(ref this) = *self;
        this.iter()
    }

    pub fn is_empty(&self) -> bool {
        let VarSet(ref this) = *self;
        this.is_empty()
    }
}

impl FromIterator<Var> for VarSet {
    fn from_iter<I: IntoIterator<Item=Var>>(iter: I) -> VarSet {
        VarSet(FromIterator::from_iter(iter))
    }
}

impl Extend<Var> for VarSet {
    fn extend<I: IntoIterator<Item=Var>>(&mut self, iter: I) {
        let VarSet(ref mut this) = *self;
        this.extend(iter)
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq, PartialOrd, Ord, Debug, Clone, Copy, Hash)]
pub enum SolutionValue { Unassigned, True, False, Conflict }

impl SolutionValue {
    fn from_bool(val: bool) -> SolutionValue {
        match val {
            true => True,
            false => False
        }
    }

    fn as_bool(&self) -> bool {
        match *self {
            True => true,
            False => false,
            otherwise => panic!("Expected True or False, got {:?}", otherwise)
        }
    }
}

/**
 * Slightly odd bitwise OR semantics that are set up to make it easier to
 * analayse a collecton of terms by ORing their values together. The
 * resulting truth table looks something like
 *
 *  OR         | True     | False      | Unassigned | Conflict |
 *  ============================================================
 *  True       | True     | True       | True       | Conflict |
 *  False      | True     | False      | Unassigned | Conflict |
 *  Unassigned | True     | Unassigned | Unassigned | Conflict |
 *  Conflict   | Conflict | Conflict   | Conflict   | Conflict |
 */
impl ops::BitOr for SolutionValue {
    type Output = SolutionValue;
    fn bitor(self, rhs: SolutionValue) -> SolutionValue {
        if self == Conflict || rhs == Conflict {
            Conflict
        }
        else if self == True || rhs == True {
            True
        }
        else if self == Unassigned || rhs == Unassigned {
            Unassigned
        }
        else {
            False
        }
    }
}

#[test]
fn unassigned_solution_value_propagates_through_or() {
    assert!((Unassigned | True) == True, "Expected True, got {:?}", Unassigned | True);
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

impl ops::Not for SolutionValue {
    type Output = SolutionValue;
    fn not(self) -> SolutionValue {
        match self {
            Unassigned => Unassigned,
            Conflict => Conflict,
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
#[derive(PartialEq, Clone)]
pub struct Solution {
    values: Vec<SolutionValue>
}

impl<'a> Solution {
    /**
     * Creates an empty solution
     */
    pub fn new(n: usize) -> Solution {
        Solution {
            values: FromIterator::from_iter(repeat(Unassigned).take(n+1))
        }
    }

    /**
     * Creates a solution from predefined values encoded as a (variable, value) pair
     */
    pub fn from(varcount: usize, values: &[(Var, SolutionValue)]) -> Solution {
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
        self.values[var] = val;
    }

    pub fn unset(&mut self, var: Var) {
        self.values[var] = Unassigned
    }

    /**
     * Resets all variables in the supplied iterator to Unassigned.
     */
    pub fn unset_all<I: Iterator<Item=Var>>(&mut self, iter: I) {
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

impl fmt::Debug for Solution {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;

        try!(write!(f, "["));
        for (k, v) in self.values.iter().enumerate() {
            if *v == Unassigned {
                continue;
            }

            if first  { first = false; } else { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}: {:?}", k, v));
        }
        write!(f, "]")
    }
}

impl ops::Index<Var> for Solution {
    type Output = SolutionValue;

    fn index<'a>(&'a self, v: &Var) -> &'a SolutionValue {
        self.values.index(v)
    }
}

impl ops::IndexMut<Var> for Solution {
    fn index_mut<'a>(&'a mut self, v: &Var) -> &'a mut SolutionValue {
        &mut self.values[*v]
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Clone, Copy)]
pub enum Term { Lit(Var), Not(Var) }

impl Term {
    pub fn var(&self) -> Var {
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

impl PartialOrd for Term {
    fn partial_cmp(&self, other: &Term) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Term) -> cmp::Ordering {
        self.var().cmp(&other.var())
    }
}

impl fmt::Debug for Term {
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


#[derive(Clone)]
pub struct Clause {
    terms: Vec<Term>
}

impl Clause {
    pub fn new() -> Clause {
        Clause { terms: vec![]}
    }

    pub fn from(terms: &[Term]) -> Clause {
        let mut v : Vec<Term> = Vec::with_capacity(terms.len());
        v.push_all(terms);
        Clause { terms: v }
    }

    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn add(&mut self, t: Term) {
        self.terms.push(t)
    }

    pub fn terms(&self) -> &[Term] {
        &self.terms[]
    }

    pub fn iter(&self) -> slice::Iter<Term> {
        self.terms.iter()
    }
}

impl FromIterator<Term> for Clause {
    fn from_iter<I: IntoIterator<Item=Term>>(terms: I) -> Clause {
        let mut r = Clause::new();
        for t in terms {
            r.add(t.clone())
        }
        r
    }
}

impl fmt::Debug for Clause {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        try!(write!(f, "("));
        for ref t in self.terms.iter() {
            if !first { try!(write!(f, " | " )); } else { first =  false; }
            try!(t.fmt(f));
        }
        write!(f, ")")
    }
}

impl PartialEq for Clause {
    fn eq(&self, other: &Clause) -> bool {
        self.terms == other.terms
    }
}

pub type ClauseId = usize;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * An expression consisting of multiple Clauses that are ANDed together.
 */
 #[derive(Clone)]
pub struct Expression {
    clauses: Vec<Clause>,
    index: VecMap<Vec<usize>>
}

/**
 * An iterator type for iterating over clauses in an expression. Turns the
 * internal representation of clauses into slices for external consumption.
 */
struct ClauseIterator<'a> {
    exp: &'a Expression,
    items: slice::Iter<'a, usize>
}

impl<'a> Iterator for ClauseIterator<'a> {
    type Item = &'a[Term];
    fn next(&mut self) -> Option<&'a[Term]> {
        match self.items.next() {
            None => None,
            Some(idx) => {
                Some(self.exp[*idx].terms().as_slice())
            }
        }
    }
}

static EMPTY_VECTOR : & 'static [usize] = &[];

impl Expression {
    pub fn new() -> Expression {
        Expression { clauses: Vec::new(), index: VecMap::new() }
    }

    /**
     * Creates an expression from a set of collections of terms
     */
    pub fn from(clauses: &[&[Term]]) -> Expression {
        let mut exp = Expression::new();

        for clause in clauses.iter() {
            exp.add_from(*clause);
        }
        exp
    }

    pub fn clauses<'a>(&'a self) -> slice::Iter<'a, Clause> {
        self.clauses.iter()
    }

    pub fn clauses_containing<'a>(&'a self, v: Var) -> ClauseIterator<'a> {
        match self.index.get(&v) {
            Some(clauses) => {
                ClauseIterator { exp: self, items: clauses.iter() }
            },
            None => {
                ClauseIterator { exp: self, items: EMPTY_VECTOR.iter() }
            }
        }
    }

    /**
     * Attempts to apply the supplied solution to the expression to see if it
     * passes.
     */
    pub fn apply(&self, sln: &Solution) -> SolutionValue {
        for clause in self.clauses() {
            let mut val = False;
            for term in clause.terms().iter() {
                val = val | term.value(sln);
            }
            match val {
                Unassigned | False => return val,
                _ => ()
            }
        }
        True
    }

    pub fn add_from(&mut self, clause: &[Term]) {
        self.add_clause(Clause::from(clause));
    }

    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
        let idx = self.clauses.len()-1;
        for t in self.clauses[idx].iter() {
            let v = t.var();
            let mut added = true;
            match self.index.get_mut(&v) {
                Some(clauses) => clauses.push(idx),
                None => added = false
            }

            if !added {
                self.index.insert(v, vec!(idx));
            }
        }
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Expression) -> bool {
        self.clauses == other.clauses
    }
}

impl fmt::Debug for Expression {
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

impl ops::Index<usize> for Expression {
    type Output = Clause;

    fn index<'a>(&'a self, index: &usize) -> &'a Clause {
        &self.clauses[*index]
    }
}

impl ops::IndexMut<usize> for Expression {
    fn index_mut<'a>(&'a mut self, index: &usize) -> &'a mut Clause {
        &mut self.clauses[*index]
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
    assert!(clauses.iter().find(|&c| c == &[Lit(1), Lit(2), Lit(3)]).is_some());
    assert!(clauses.iter().find(|&c| c == &[Lit(1)]).is_some())
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