use std::collections::{TrieMap, TrieSet};
use std::collections::trie::{Entries, Keys};
use std::fmt;
use log;
use solver::types::{SolutionValue, True, False, Unassigned};
use solver::types::{Term, Lit, Not};
use solver::types::{Solution, Expression, Var};

type VarSet = TrieSet;

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[deriving(Show, PartialEq)]
struct ImplicationMap(TrieMap<SolutionValue>);

impl ImplicationMap {
    fn new() -> ImplicationMap {
        ImplicationMap(TrieMap::new())
    }

    fn value_of(&self, v: Var) -> SolutionValue {
        let ImplicationMap(ref me) = *self;
        match me.find(&v) {
            None => Unassigned,
            Some(rval) => *rval 
        }
    }

    fn add(&mut self, var: Var, val: SolutionValue) {
        let ImplicationMap(ref mut me) = *self;
        me.insert(var, val);
    }

    fn is_empty(&self) -> bool {
        let ImplicationMap(ref me) = *self;
        me.is_empty()
    }

    fn iter<'a>(&'a self) -> Entries<'a, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.iter()   
    }

    fn vars<'a>(&'a self) -> Keys<'a, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.keys()
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

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

// ----------------------------------------------------------------------------
// Solve state tracking
// ----------------------------------------------------------------------------

#[deriving(Show)]
struct SolveState {
    var: uint,
    value: SolutionValue,
    implications: ImplicationMap
}

struct StateStack {
    stack: Vec<SolveState>
}

impl StateStack {
    fn new() -> StateStack { 
        StateStack { stack: Vec::new() } 
    }

    fn new_with_unassigned(var: Var) -> StateStack {
        let mut s = StateStack::new();
        s.push_unassigned(var);
        s
    }

    fn push(&mut self, 
            var: Var, 
            value: SolutionValue,
            implications: ImplicationMap) {
        self.stack.push( SolveState {
            var: var, 
            value: value, 
            implications: implications
        });
    }

    fn push_unassigned(&mut self, var: Var) {
        self.stack.push( SolveState {
            var: var, 
            value: Unassigned, 
            implications: ImplicationMap::new()
        });
    }

    fn pop(&mut self) -> Option<SolveState> {
        self.stack.pop()
    }
}

impl Collection for StateStack {
    fn len(&self) -> uint { self.stack.len() }
    fn is_empty(&self) -> bool { self.stack.is_empty() }
}

impl Index<uint, SolveState> for StateStack {
    fn index<'a>(&'a self, index: &uint) -> &SolveState {
        &self.stack[*index]
    }
}

impl fmt::Show for StateStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, s) in self.stack.iter().enumerate() {
            try!(write!(f, "{}: {}", i, s))
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn try_assignment(state: SolveState, 
                  stack: &mut StateStack, 
                  unassigned_vars: &mut VarSet,
                  exp: &Expression, 
                  sln: &mut Solution) -> bool {
    let var = state.var;
    let val = next_val(state.value);

    debug!("\tAttempting to set {} = {}", var, val);

    sln.set(var, val);
    unassigned_vars.remove(&var);

    match propagate(sln, var, val, exp) {
        // Yay - the assinment of var = val was valid. Time to update the bookkeeping. 
        Success (implications) => {

            // remove all variables that we assigned values to in this pass 
            // from the unassigned variables set.
            for (k, _) in implications.iter() {
                unassigned_vars.remove(&k);
            }

            // Push a record of what we did to the stack to allow for 
            // backtraking if need be.
            stack.push(var, val, implications);

            // if we still have work to do...
            if !unassigned_vars.is_empty() {
                debug!("\tSelecting new var");
                let v = pick_var(unassigned_vars);
                stack.push_unassigned(v);
            }

            true
        },

        // Any sort of failure - get set up for the next pass by pushing a copy of our 
        // original state with an updated value to try  
        _ => {
            debug!("Assignment failed.");
            if val == False {
                debug!("Setting up for retry");
                stack.push(var, val, ImplicationMap::new());
            }
            else {
                debug!("Setting up for Backtracking");
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
    let mut stack = StateStack::new_with_unassigned(5);
    let mut vars = TrieSet::new();
    for v in [1, 2, 3, 4, 6].iter() {
        vars.insert(*v);
    }
    let mut sln = Solution::new(6);
    assert!(try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &exp, &mut sln));
    assert!(stack.len() == 2);

    assert!(stack[1].value == Unassigned);
    assert!(stack[1].var != 5);
    assert!(stack[1].implications.is_empty());

    assert!(sln[5] == False);
    
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
    let mut stack = StateStack::new_with_unassigned(1);
    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }
    let mut sln = Solution::new(6);
    assert!(!try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &exp, &mut sln));
    assert!(stack.len() == 1);

    assert!(stack[0].value == False);
    assert!(stack[0].var == 1);
    assert!(stack[0].implications.is_empty());

    assert!(sln[1] == Unassigned);

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

    let mut stack = StateStack::new();
    stack.push(1, False, ImplicationMap::new());

    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }

    let mut sln = Solution::new(6);
    assert!(try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &exp, &mut sln));
    assert!(stack.len() == 2);

    assert!(stack[0].var == 1);
    assert!(stack[0].value == True);
    assert!(stack[0].implications.value_of(1) == True, 
            "Expected {}, got {}", True, stack[0].implications.value_of(1));

    assert!(stack[1].value == Unassigned);
    assert!(stack[1].var != 5);
    assert!(stack[1].implications.is_empty());

    assert!(sln[1] == True);

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

    let mut stack = StateStack::new();
    stack.push(1, False, ImplicationMap::new());

    let mut vars = TrieSet::new();
    for v in [2, 3, 4, 5, 6].iter() {
        vars.insert(*v);
    }

    let mut sln = Solution::new(6);
    assert!(!try_assignment(stack.pop().unwrap(), &mut stack, &mut vars, &exp, &mut sln));
}

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
pub fn solve(e: &Expression, 
             varcount: uint, 
             initial_sln: Solution) -> Option<Solution> {
    let mut unassigned_vars = scan_unassigned_vars(varcount, &initial_sln);
    let mut stack = StateStack::new();
    let mut sln = initial_sln.clone(); 

    stack.push_unassigned( pick_var(&mut unassigned_vars));
    while !unassigned_vars.is_empty() {
        if stack.is_empty() { return None; }
        let state = stack.pop().unwrap();

        // undo whatever was done at the time this record was pushed onto the 
        // stack. If this is a new variable then this will be empty. If we are 
        // bactracking then it may well have content.
        for (k, _) in state.implications.iter() {
            sln.set(k, Unassigned);
            unassigned_vars.insert(k);
        }

        debug!("Stack depth: {}", stack.len());
        if log_enabled!(log::INFO) {
            let unv : Vec<uint> = FromIterator::from_iter(unassigned_vars.iter());
            debug!("Unassigned vars: {}", unv);

            debug!("Solution: {}", sln);
        }

        //
        match state.value {
            Unassigned | False => {
                try_assignment(state, &mut stack, &mut unassigned_vars, e, &mut sln);
            },

            // We have tried both forks. Time to backtrack
            True => {
                debug!("<<< backtracking detected >>>");
                if stack.is_empty() { 
                    debug!("No solution found");
                    return None; 
                }
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

    match solve(&exp, 7, Solution::new(7)) {
        None => { fail!("Expression should be valid"); }
        Some(sln) => {
            debug!("Solution: {}", sln);

            assert!(range(1u, 8u).all(|x| sln[x] != Unassigned));
            assert!(exp.apply(&sln) == True);
            assert!(sln[1] == True); // this at least must be true

            match sln.get(2) {
                False => { 
                    assert!(sln[6] == False, "If 2 is false then 5 *must* be true");
                    assert!((sln[3] | sln[4]) == True, "If 2 is false then 3 | 4 *must* be true");
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

    match solve(&exp, 7, Solution::new(7)) {
        None => { }
        Some(_) => { 
            fail!("Expression contains a contradiction, so shouldn't succeed.")
        }
    }
}

enum ClauseAnalysis {
    IsTrue, IsFalse, IsUnit (Term), IsIndeterminate
}

fn analyse_clause(clause: &[Term], sln: &Solution) -> ClauseAnalysis {
    let mut value = False;
    let mut unassigned_terms = Vec::with_capacity(clause.len());

    // walk each term in the Clause and try to evaluate it.
    for term in clause.iter() {
        let t = term.value(sln);
        value = value | t;

        if t == Unassigned {
            unassigned_terms.push(term);
        }

        if value == True {
            break;
        }
    }

    match value {
        True => IsTrue,
        False => IsFalse,
        Unassigned => {
            assert!(unassigned_terms.len() > 0);

            if unassigned_terms.len() == 1 {
                IsUnit(*unassigned_terms[0])
            }
            else {
                IsIndeterminate
            }
        }
    }
}

#[deriving(Show)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * 
     */
    Contradiction (uint),

    /**
     * (implications) where
     *
     *   implications - A dictionary of the values deduced from this 
     *                  propagation pass.
     */
    Success (ImplicationMap)
}

/**
 *
 */
fn propagate(sln: &mut Solution, seed_var: Var, seed_val: SolutionValue, e: &Expression) -> PropagationResult {
    let mut implications = ImplicationMap::new();
    let mut queue : Vec<(Var, SolutionValue)> = Vec::new();
    queue.push((seed_var, seed_val));
    implications.add(seed_var, seed_val);

    while !queue.is_empty() {
        let (var, val) = queue.pop().unwrap();

        debug!("\tChecking implications of setting {} = {}", var, val)

        sln.set(var, val);

        for clause in e.clauses_containing(var) {
            match analyse_clause(clause, sln) {
                IsUnit (term) => {
                    debug!("\t\tFound unit clause {}, term of interest is {}", clause, term)
                    let v = term.var();

                    // deduce value
                    let deduced_value = match term {
                        Lit (_) => True,
                        Not (_) => False
                    };

                    debug!("\t\tDeduced that {} = {}", v, deduced_value);

                    // check for a contradiction - have we aleady deduced that 
                    // this variable must have a different value?
                    debug!("\t\tExisting implication for {} is {}", v, implications.value_of(v));
                    match implications.value_of(v) {
                        Unassigned => { 
                            queue.push((v, deduced_value));
                            implications.add(v, deduced_value);
                        },

                        x if x != deduced_value => { 
                            debug!("\t\tDetected contradiction on {}!", v);
                            sln.unset_all(implications.vars());
                            return Contradiction(v) 
                        },

                        _ => { /* value is consistent, all is well */ }
                    }
                },

                IsTrue => { 
                    debug!("\t\tClause {} is TRUE", clause);
                },

                IsFalse => {
                    // oh, dear. All variables in the term have values and the
                    // clause evaluates to false. Bail out and let the caller 
                    // know that this can't possibly be the right answer.
                    debug!("\t\tClause {} evaluates to false. Ooops.", clause); 
                    sln.unset_all(implications.vars());
                    return EvaluatesToFalse
                },

                IsIndeterminate => { 
                    debug!("\t\tClause {} is still indeterminate", clause);
                }
            }
        }
    }

    Success (implications)
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    match propagate(&mut sln, 4, False, &exp) {
        Success (implications) => {
            let mut expected_implications = ImplicationMap::new();
            expected_implications.add(3u, True); 
            expected_implications.add(4u, False); 
            assert!(implications == expected_implications, 
                "Expected {}, got {}", expected_implications, implications)
        },
        other => {
            fail!("Unexpected propagation result: {}", other)
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);
    let mut sln = Solution::from(4, &[(1, False), (2, False)]);
    match propagate(&mut sln, 4, False, &exp) {
        Success (implications) => {
            let mut expected_implications = ImplicationMap::new();
            expected_implications.add(3u, False); 
            expected_implications.add(4u, False);
            assert!(implications == expected_implications,
                "Expected {}, got {}", expected_implications, implications)
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

    let mut sln = Solution::from(3, &[(1, False)]);
    
    match propagate(&mut sln, 2, False, &exp) {
        Contradiction (n) => assert!(n == 3, "Expected a contractiction of variable #3"),
        other => fail!("Unexpected result from propagate(): {}", other)
    }

    assert!(sln[1] == False, "Expected False, got {}", sln[1]);
    assert!(sln[2] == Unassigned, "Expected Unassigned, got {}", sln[2]);
    assert!(sln[3] == Unassigned, "Expected Unassigned, got {}", sln[3]);
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let mut sln = Solution::from(4, &[(1, False), (2, False)]);

    match propagate(&mut sln, 3, False, &exp) {
        EvaluatesToFalse => {},
        other => fail!("Unexpected result from propagate(): {}", other)
    }
}
