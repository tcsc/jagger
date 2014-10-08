use std::collections::{TreeMap, TrieSet};
use std::collections::treemap::{Entries};
use std::fmt;
use std::rc::Rc;
use std::slice;
use log;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
type Var = uint;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(PartialEq, Eq, Show)]
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

impl Not<SolutionValue> for SolutionValue {
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

/**
 * A variable-to-value mapping.
 */
#[deriving(PartialEq, Clone)]
pub struct Solution (TreeMap<Var, bool>);

impl<'a> Solution {
    /**
     * Creates an empty solution
     */
    pub fn new() -> Solution { Solution(TreeMap::new()) }

    /**
     * Creates a solution from predefined values encoded as a (variable, value) pair
     */
    pub fn from(values: &[(Var, SolutionValue)]) -> Solution {
        let mut s = Solution::new();
        for &(var, val) in values.iter() {
            s.set(var, val)
        }
        s
    }

    /**
     * Sets a value in the solution
     */
    pub fn set(&mut self, var: Var, val: SolutionValue) {
        let Solution(ref mut map) = *self;
        match val {
            Unassigned => map.remove(&var),
            _ => map.insert(var, val.as_bool())
        };
    }

    /**
     * Fetches a value in the solution
     */
    pub fn get(&self, var: Var) -> SolutionValue {
        let Solution(ref map) = *self;
        match map.find(&var) {
            Some(val) => SolutionValue::from_bool(*val),
            None => Unassigned
        }
    }

    pub fn assigned_vars(&self) -> Vec<Var> {
        let Solution(ref map) = *self;
        map.iter().map(|(k, _)| *k).collect()
    }

    pub fn is_assigned(&self, v: Var) -> bool {
        let Solution(ref map) = *self;
        map.contains_key(&v)
    }

    pub fn iter(&'a self) -> Entries<'a, Var, bool> {
        let Solution(ref map) = *self;
        map.iter()
    }
}

impl fmt::Show for Solution {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        let Solution(ref map) = *self;
        try!(write!(f, "["));
        for (k, v) in map.iter() {
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

    fn add_ref(&mut self, clause: &Rc<Clause>) {
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

type VarSet = TrieSet;
type ImplicationMap = TreeMap<uint, SolutionValue>;

#[deriving(Show)]
struct SolveState {
    var: uint,
    value: SolutionValue,
    expression: Expression,
    implications: ImplicationMap
}

impl SolveState {
    fn new(exp: Expression, 
           var: uint, 
           value: SolutionValue, 
           implications: ImplicationMap) -> SolveState {
        SolveState { 
            var: var, 
            value: value, 
            implications: implications,
            expression: exp
        }
    }

    fn new_unassigned(e: Expression, var: uint) -> SolveState {
        SolveState {
            var: var, 
            value: Unassigned, 
            implications: TreeMap::new(), 
            expression: e
        }
    }
}

/**
 * Chooses the next variable to assign from the set.
 */
fn pick_var(vars: &VarSet) -> uint {
    vars.iter().next().unwrap()
}

fn scan_unassigned_vars(varcount: uint, sln: &Solution) -> VarSet {
    let mut result = TrieSet::new();
    for v in range(1, varcount+1) {
        if !sln.is_assigned(v) { result.insert(v); }
    }
    result
}

fn next_val(v: SolutionValue) -> SolutionValue {
    match v { 
        Unassigned => False, 
        False => True, 
        _ => fail!("next_val was called with True") 
    }
}

#[test]
fn nextval_progresses_correctly() {
    assert!(next_val(Unassigned) == False);
    assert!(next_val(False) == True);      
}

#[test] 
#[should_fail]
fn nextval_fails_on_overrun() {
    next_val(True);
}

type StateStack = Vec<SolveState>;

fn try_assignment(state: SolveState, stack: &mut StateStack, unassigned_vars: &mut VarSet, sln: &mut Solution) -> bool {
    let var = state.var;
    let val = next_val(state.value);
    let exp = state.expression;

    debug!("\tAttempting to set {} = {}", var, val);

    sln.set(var, val);
    unassigned_vars.remove(&var);

    match propagate(sln, &exp) {
        // Yay - the assinment of var = val was valid. Time to update the bookkeeping. 
        Success (new_exp, mut implications) => {
            implications.insert(var, val);

            debug!("\tOriginal expression: {}", exp);
            debug!("\tSimplified expression: {}", new_exp);

            // remove all variables that we assigned values to in this pass 
            // from the unassigned variables set.
            for (k, v) in implications.iter() {
                unassigned_vars.remove(k);
                sln.set(*k, *v);
            }

            // we're effectively done; if we already know the expression will 
            // evaluate to True then the values of all the currenylt unassigned 
            // variables don't matter. 
            if new_exp.is_empty() {
                debug!("All clauses in the expression have been evaluated.")

                // set all unassigned vars to false - we don't want to install
                // things that don't need to be installed. 
                for v in unassigned_vars.iter() {
                    sln.set(v, False)
                }

                // everything is now assigned. woot.
                unassigned_vars.clear();
            }


            // Push a record of what we did to the stack to allow for 
            // backtraking if need be.
            stack.push( SolveState::new(exp, var, val, implications) );

            // if we still have work to do...
            if !unassigned_vars.is_empty() {
                debug!("\tSelecting new var");
                stack.push( SolveState::new_unassigned(new_exp, pick_var(unassigned_vars)));
            }

            true
        },

        // Any sort of failure - get set up for the next pass by pushing a copy of our 
        // original state with an updated value to try  
        _ => {
            debug!("Assignment failed.");
            if val == False {
                debug!("Setting up for retry");
                stack.push( SolveState::new(exp, var, val, TreeMap::new()) );
            }
            else {
                debug!("Backtracking");
            }

            sln.set(var, Unassigned);
            unassigned_vars.insert(var);

            false
        }
    }
}

#[test]
fn trying_valid_assignment_on_new_var_succeeds() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);
    let mut stack = vec![SolveState::new_unassigned(exp, 5)];
    let mut vars = TrieSet::new();
    for v in [1, 2, 3, 4, 6].iter() {
        vars.insert(*v);
    }
    let mut sln = Solution::new();
    assert!(try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &mut sln));
    assert!(stack.len() == 2);

    assert!(stack.get(1).value == Unassigned);
    assert!(stack.get(1).var != 5);
    assert!(stack.get(1).implications.is_empty());

    assert!(sln.get(5) == False);
    
    debug!("Stack: {}", stack);
}

#[test]
fn trying_invalid_assignment_on_new_var_fails() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);
    let mut stack = vec![SolveState::new_unassigned(exp, 1)];
    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }
    let mut sln = Solution::new();
    assert!(!try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &mut sln));
    assert!(stack.len() == 1);

    assert!(stack.get(0).value == False);
    assert!(stack.get(0).var == 1);
    assert!(stack.get(0).implications.is_empty());

    assert!(sln.get(1) == Unassigned);

    debug!("Stack: {}", stack);
}

#[test]
fn trying_valid_backtracked_assignment_succeeds() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut stack = vec![SolveState::new(exp, 1, False, TreeMap::new())];

    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }

    let mut sln = Solution::new();
    assert!(try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &mut sln));
    assert!(stack.len() == 2);


    assert!(stack.get(0).var == 1);
    assert!(stack.get(0).value == True);
    assert!(stack.get(0).implications.contains_key(&1));

    assert!(stack.get(1).value == Unassigned);
    assert!(stack.get(1).var != 5);
    assert!(stack.get(1).implications.is_empty());

    assert!(sln.get(1) == True);

    debug!("Stack: {}", stack);
}

#[test]
fn trying_invalid_backtracked_assignment_fails() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut stack = vec![SolveState::new(exp, 1, False, TreeMap::new())];

    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }

    let mut sln = Solution::new();
    assert!(!try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &mut sln));

    debug!("Stack: {}", stack);
}

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
fn solve(e: &Expression, varcount: uint, initial_sln: Solution) -> Option<Solution> {
    let mut unassigned_vars = scan_unassigned_vars(varcount, &initial_sln);
    let mut stack : Vec<SolveState> = Vec::new();
    let mut sln = initial_sln.clone(); 

    stack.push( SolveState::new_unassigned((*e).clone(), pick_var(&mut unassigned_vars)) );
    while !unassigned_vars.is_empty() {
        if stack.is_empty() { return None; }
        let state = stack.pop().unwrap();

        // undo whatever was done at the time this record was pushed onto the 
        // stack. If this is a new variable then this will be empty. If we are 
        // bactracking then it may well have content.
        for (k, _) in state.implications.iter() {
            sln.set(*k, Unassigned);
            unassigned_vars.insert(*k);
        }

        debug!("Stack depth: {}", stack.len());
        debug!("Next target: {}", state.var);
        if log_enabled!(log::INFO) {
            let unv : Vec<uint> = FromIterator::from_iter(unassigned_vars.iter());
            debug!("Unassigned vars: {}", unv);
        }

        //
        match state.value {
            Unassigned | False => {
                try_assignment(state, &mut stack, &mut unassigned_vars, &mut sln);
            },

            // We have tried both forks. Time to backtrack
            True => {
                if stack.is_empty() { 
                    return None; 
                }
                stack.pop();
            }
        }
    }

    Some(sln)
}

#[test]
fn solver_completes() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3), Lit(4)],
        &[Lit(1), Not(7)],
        &[Lit(3)],
        &[Not(2), Not(3)],
        &[Not(3), Lit(2), Lit(1)],
        &[Not(1), Lit(3)], 
        &[Not(2), Lit(7)],
        &[Not(4)],
    ]);

    match solve(&exp, 7, Solution::new()) {
        None => { fail!("Expression should be valid"); }
        Some(sln) => {
            debug!("Solution: {}", sln);

            assert!(range(1u, 8u).all(|x| sln.get(x) != Unassigned));
            assert!(exp.apply(&sln) == True);
            assert!(sln.get(1) == True); // this at least must be true

            match sln.get(2) {
                False => { 
                    assert!(sln.get(6) == False, "If 2 is false then 5 *must* be true");
                    assert!((sln.get(3) | sln.get(4)) == True, "If 2 is false then 3 | 4 *must* be true");
                }
                _ => {}
            }
        }
    }
}

#[test]
fn solver_detects_basic_contradiction() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3), Lit(4)],
        &[Lit(3)],
        &[Not(3)],
        &[Not(2), Not(3)],
        &[Not(3), Lit(2), Lit(1)],
        &[Not(1), Lit(3)], 
        &[Not(2), Lit(7)],
        &[Not(4)],
    ]);

    match solve(&exp, 7, Solution::new()) {
        None => { }
        Some(sln) => { 
            fail!("Expression contains a contradiction, so shouldn't succeed.")
        }
    }
}


// #[test]
// fn solver_detects_basic_contradiction() {
//     let e = Expression::from([ &[Lit(1)], &[Not(1)]]);
//     match solve(&e, TrieSet::new()) {
//         Some(s) => fail!("Expected a contradiction, got {0}", s),
//         None => assert!(true)
//     }
// }

#[deriving(Show)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * 
     */
    Contradiction (uint),

    /**
     * (new_exp, implications) where
     *
     *   new_exp - An abbbreviated version of the input expression, where all
     *             Clauses proven to be true have been removed.
     *
     *   implications - A dictionary of the values deduced from this 
     *                  propagation pass.
     */
    Success (Expression, ImplicationMap)
}

/**
 *
 */
fn propagate(sln: &Solution, e: &Expression) -> PropagationResult {
    let mut new_exp = Expression::new();
    let mut implications = TreeMap::new();
        
    debug!("\t\tInput expression: {}", e);
    debug!("\t\tInput solution: {}", sln);
    
    for clause in e.iter() {
        let mut value = False;
        let mut unassigned_terms = Vec::with_capacity(clause.len());

        // walk each term in the Clause and try to evaluate it.
        for term in clause.terms() {
            match term.value(sln) {
                Unassigned => { unassigned_terms.push(term) },
                v => { value = value | v; }
            }

            if value == True { break }
        }

        // decide what to do based on out evaluation attempt above
        match value {
            True => {
                // At least one term in the Clause evaluates to true, meaning 
                // that the entire Clause does. This in turn means that the 
                // entire Clause can be removed from the expression and so reduce
                // the search space for the next time around. 

                // Watch us explicitly not copy the Clause into the output 
                // expression.
                debug!("\t\tEliminiating clause {}", clause);
            },

            False => {
                match unassigned_terms.len() {
                    // oh, dear. All variables in the term have values and the
                    // Clause evaluates to false. Bail out and let the caller 
                    // know that this can't possibly be the right answer.
                    0 => {
                        debug!("\t\tClause {} evaluates to false. Ooops.", clause); 
                        return EvaluatesToFalse 
                    },

                    // We have a 'unit' Clause (i.e. all terms bar one are 
                    // false). We can infer a value for the remaining value and
                    // propagate that.
                    1 => {
                        debug!("\t\tExamining unit Clause: {}", clause);

                        let term = *unassigned_terms.get(0);
                        let var = term.var();

                        // deduce value
                        let deduced_value = match *term {
                            Lit (_) => True,
                            Not (_) => False
                        };

                        debug!("\t\tDeduced that {} = {}", var, deduced_value);

                        // check for a contradiction
                        if !implications.contains_key(&var) {
                            implications.insert(var, deduced_value);
                        }
                        else {
                            match implications.find(&var) {
                                Some(x) if (*x) != deduced_value => { 
                                    debug!("\t\tDetected contradiction on {}!", var);
                                    return Contradiction(var) 
                                },
                                Some(_) => { /* value is consistent, all is well */ },
                                None => fail!("Inconsistent implication map")
                            }
                        }

                        // watch us once again not copy the input clause to the
                        // output expression, as we now know that the clause 
                        // evaluates to true.
                        debug!("\t\tEliminiating unit clause {}", clause);
                    },

                    // We have multiple unassigned variables in the Clause; not 
                    // much we can do here except wait for more letters in the 
                    // crossword.
                    _ => {
                        // copy the Clause into the output expression
                        new_exp.add_ref(clause);
                    }
                };
            },

            Unassigned => { 
                fail!("Clause evaluates to unassigned. This should have been expressly forbidden."); 
            }
        }
    }

    Success (new_exp, implications)
}

#[test]
fn propagation_eliminates_true_clauses() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let sln = Solution::from(&[(1, False), (2, False), (5, True)]);
    match propagate(&sln, &exp) {
        Success (new_exp, _) => {
            let expected = Expression::from(&[
                &[Lit(2), Lit(3), Lit(4)]
            ]);
            assert!(new_exp == expected, "Expected {}, got {}", expected, new_exp);
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let sln = Solution::from(&[(1, False), (2, False), (4, False)]);
    match propagate(&sln, &exp) {
        Success (new_exp, implications) => {
            let expected_expression = Expression::new();
            assert!(expected_expression == new_exp, "Expected {}, got {}", expected_expression, new_exp);

            let mut expected_implications = TreeMap::new();
            expected_implications.insert(3u, True); 
            assert!(implications == expected_implications)
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);
    let sln = Solution::from(&[(1, False), (2, False), (4, False)]);
    match propagate(&sln, &exp) {
        Success (new_exp, deduced_values) => {
            let expected_expression = Expression::new();
            assert!(new_exp == expected_expression, "Expected {}, got {}", expected_expression, new_exp);

            let mut expected_implications = TreeMap::new();
            expected_implications.insert(3u, False); 
            assert!(deduced_values == expected_implications);
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_detects_contradictions() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(3)],
    ]);

    let sln = Solution::from(&[(1, False), (2, False)]);

    match propagate(&sln, &exp) {
        Contradiction (n) => assert!(n == 3, "Expected a contractiction of variable #3"),
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let sln = Solution::from(&[(1, False), (2, False), (3, False)]);

    match propagate(&sln, &exp) {
        EvaluatesToFalse => {},
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}