use std::collections::HashMap;
use std::collections::hash_map::{Keys, Iter};
use std::iter::{FromIterator, range_step};
use std::ops::Index;
use std::fmt;
use log;

use solver::types::{Solution, SolutionValue, Expression, Var, VarSet, Clause, Term};
use solver::types::SolutionValue::{Unassigned, True, False, Conflict};
use solver::types::Term::{Lit, Not};
use solver::implication_graph::{ImplicationGraph, dump_graph};
use solver::brancher::{Brancher, NaiveBrancher};
use collections::{VecSet, VecMap};

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
struct ImplicationMap(HashMap<Var, SolutionValue>);

impl ImplicationMap {
    fn new() -> ImplicationMap {
        ImplicationMap(HashMap::new())
    }

    fn value_of(&self, v: Var) -> SolutionValue {
        let ImplicationMap(ref me) = *self;
        match me.get(&v) {
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

    fn iter<'a>(&'a self) -> Iter<'a, Var, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.iter()
    }

    fn vars<'a>(&'a self) -> Keys<'a, Var, SolutionValue> {
        let ImplicationMap(ref me) = *self;
        me.keys()
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn next_val(v: SolutionValue) -> SolutionValue {
    match v {
        Unassigned => False,
        False => True,
        _ => panic!("next_val was called with True")
    }
}

#[test]
fn nextval_progresses_correctly() {
    assert!(next_val(Unassigned) == False);
    assert!(next_val(False) == True);
}

#[test]
#[should_panic]
fn nextval_fails_on_overrun() {
    next_val(True);
}

// ----------------------------------------------------------------------------
// Solve state tracking
// ----------------------------------------------------------------------------

struct DecisionStack {
    stack: Vec<Var>
}

impl DecisionStack {
    fn new() -> DecisionStack {
        DecisionStack { stack: Vec::new() }
    }

    fn push(&mut self, var: Var) {
        self.stack.push(var);
    }

    fn peek(&self) -> Option<&Var> {
        self.stack.last()
    }

    fn mut_peek(&mut self) -> Option<&mut Var> {
        match self.stack.len() {
            0 => None,
            n => Some(&mut self.stack[n-1])
        }
    }

    fn pop(&mut self) -> Option<Var> {
        self.stack.pop()
    }

    fn len(&self) -> usize { self.stack.len() }
    fn is_empty(&self) -> bool { self.stack.is_empty() }
}

impl Index<usize> for DecisionStack {
    type Output = Var;
    fn index<'a>(&'a self, index: &usize) -> &'a Var {
        &self.stack[*index]
    }
}

impl fmt::Debug for DecisionStack {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (i, s) in self.stack.iter().enumerate() {
            try!(write!(f, "{:?}: {:?}", i, s))
        }
        Ok(())
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[cfg(test)]
fn mk_graph_test_exp() -> Expression {
    Expression::from(&[
        &[Lit(1), Lit(4)],
        &[Lit(1), Not(3), Not(8)],
        &[Lit(1), Lit(8), Lit(12)],
        &[Lit(2), Lit(11)],
        &[Not(7), Not(3), Lit(9)],
        &[Not(7), Lit(8), Not(9)],
        &[Lit(7), Lit(8), Not(10)],
        &[Lit(7), Lit(10), Not(12)]
    ])
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------


#[test]
fn trying_valid_assignment_on_new_var_succeeds() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Not(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(6),
        solution: Solution::new(6),
        implications: ImplicationGraph::new(),
        stack: DecisionStack::new()
    };

    assert!(propagate(1, 5, False, &mut state, &exp).is_success());
    assert!(state.solution[5] == False);
    assert!(state.brancher.contains(5));
    assert!(!state.brancher.contains(2));
    assert!(!state.brancher.contains(6));
}

#[test]
fn trying_invalid_assignment_on_new_var_fails() {
    let exp = Expression::from(&[
        &[Lit(2), Lit(3), Lit(4)],
        &[Lit(1)],
        &[Lit(5), Lit(6)],
        &[Lit(2), Not(6)]
    ]);

    let mut brancher = NaiveBrancher::new(6);
    let mut state = SolveState::new(6, &mut brancher);

    assert!(propagate(1, 1, False, &mut state, &exp).is_failure());
    assert!(state.solution[1] == False);
    assert!((1..6).all(|x| state.brancher.contains(x)));

    // assert!(state.unassigned_vars == expected_vars,
    //         "Expected {:?}, Got {:?}", expected_vars, state.unassigned_vars);
//    panic!("fix this test");
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

enum SolverMove { Continue, Backtrack, Retry (Var, SolutionValue) }

struct SolveState<'a> {
    brancher: &'a mut Brancher,
    implications: ImplicationGraph,
    solution: Solution,
    stack: DecisionStack
}

impl<'a> SolveState<'a> {
    fn new(varcount: usize, brancher: &'a mut Brancher) -> SolveState<'a> {
        SolveState {
            brancher: brancher,
            implications: ImplicationGraph::new(),
            solution: Solution::new(varcount),
            stack: DecisionStack::new()
        }
    }

    fn has_unassigned_vars(&self) -> bool {
        !self.brancher.is_empty()
    }

    fn undo_decision(&mut self, v: &Var) -> Vec<Var> {
        debug!("Undoing {:?}", v);

        let mut vars = self.implications.strip(*v, False);
        vars.extend(self.implications.strip(*v, True)
                                     .iter()
                                     .map(|&x| x));
        debug!("Vars to unset {:?}", vars);

        for k in vars.iter() {
            self.solution.unset(*k);
            self.brancher.insert(*k);
        }

        FromIterator::from_iter(vars.iter().map(|&x|x))
    }

    fn push(&mut self, var: Var) {
        self.stack.push(var);
        self.brancher.remove(var);
    }

    fn pop(&mut self) -> Option<Var> {
        self.stack.pop()
    }

    fn mut_peek(&mut self) -> Option<&mut Var> {
        self.stack.mut_peek()
    }

    fn depth(&self) -> usize {
        self.stack.len()
    }

    /**
     * Unwinds the state stack until all decisions affecting the variables in
     * the supplied set have been undone. Fails hard if the unwinding tries to
     * go past the end of the stack.
     */
    fn unwind(&mut self, mut vars: VecSet<Var>) {
        debug!("Unwinding for: {:?}", vars);
        while !vars.is_empty() {
            match self.pop() {
                None => panic!("Attempting to unwind an empty stack"),
                Some(d) => {
                    let vars_to_reset = self.undo_decision(&d);
                    for v in vars_to_reset.iter() {
                        vars.remove(v);
                    }
                }
            }
        }
    }

    /**
     * Backtracks until
     */
    fn backtrack(&mut self) -> Option<(Var, SolutionValue)> {
        loop {
            match self.pop() {
                // we've got to the end of the stack, the whole thing is
                // unsatisfiable
                None => return None,

                Some(d) => {
                    let value = self.solution[d];
                    self.undo_decision(&d);

                    // If the original decision set the value to False, we can try it again
                    // with True. Otherwise we try and backtrack again.
                    if value == False { return Some((d, True)) }
                    // else { bactrack again }
                }
            }
        }
    }

    fn level(&self) -> usize {
        self.stack.len()
    }
}

#[test]
fn stack_unwound_to_expected_point() {
    use solver::implication_graph;

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(10),
        implications: ImplicationGraph::new(),
        solution: Solution::new(10),
        stack: DecisionStack::new()
    };

    // Create a history for the test
    for (level, x) in range_step(1, 11, 2).enumerate() {
        state.push(x);
        state.solution.set(x, True);
        state.solution.set(x+1, False);
        state.implications.insert(level, x, True, &[]);
        state.implications.insert(level, x+1, False, &[(x,True)]);
    }

    // roll back the decision stack such that all of the supplied variables
    // are unset.
    let missing_vars : VecSet<Var> = FromIterator::from_iter(
        [10, 5, 8].iter().map(|x| *x));

    // check that the unwind returns the last decision variable it unset
    // during the rollback
    state.unwind(missing_vars);

    // Check that the decision stack is now the size we expect from a
    // post-rollback stack
    assert!(state.stack.len() == 2);

    // assert that all variables prior to the rollback point are still
    // assigned
    assert!((1..5).all(|n| state.solution[n] != Unassigned));

    // assert that all variables after the rollback point have been unassigned
    // and their implications have been deleted
    assert!((5..11).all(|n| state.solution[n] == Unassigned));
    assert!((5..11).all(|n| !state.implications.has(n)));

    assert!(4 == state.implications.len(),
        "Expected a 4-element implication graph, got {:?}",
        state.implications.len());
}

/**
 * The main solver routine. Horribly side-effecting, but only internally.
 */
pub fn solve(exp: &Expression,
             varcount: usize,
             initial_sln: Solution) -> Option<Solution> {
    let mut brancher = NaiveBrancher::new(varcount);
    let mut state = SolveState::new(varcount, &mut brancher);
    let mut next_move = SolverMove::Continue;
    let mut e = exp.clone();

    debug!("Starting solve");

    while state.has_unassigned_vars() {
        let (decision_var, decision_val) = match next_move {
            SolverMove::Continue => state.brancher.pick_branch().unwrap(),
            SolverMove::Retry (x, v) => (x, v),
            SolverMove::Backtrack => {
                match state.backtrack() {
                    Some((x, v)) => (x, v),
                    None => return None
                }
            }
        };

        state.push(decision_var);

        println!("Decision: {:?} = {:?}, Stack depth: {:?}", decision_var, decision_val, state.stack.len());

        match propagate(state.depth(), decision_var, decision_val, &mut state, &e) {
            PropagationResult::Success => {
                next_move = SolverMove::Continue;
            },

            PropagationResult::Contradiction (conflict) => {
                debug!("Contradiction");
                if state.level() == 1 {
                    // oops - UNSAT
                    return None
                }
                else {
                    let new_rule = state.implications.learn_conflict_clause(
                                        decision_var,
                                        decision_val,
                                        conflict);
                    debug!("Learned {:?}", new_rule);
                    let mut vars_to_reset = VecSet::with_capacity(new_rule.len());
                    vars_to_reset.extend(new_rule.iter().map(|t| t.var()));
                    e.add_clause(new_rule);
                    state.unwind(vars_to_reset);
                    next_move = SolverMove::Continue;
                }
            },

            PropagationResult::EvaluatesToFalse => {
                debug!("Evaluates to false");
                next_move = SolverMove::Backtrack;
            }
        }
    }

    Some(state.solution)
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
        None => { panic!("Expression should be valid"); }
        Some(sln) => {
            debug!("Solution: {:?}", sln);

            println!("+++ {:?}, {:?}", sln, (1..8).all(|x| {
                println!(">>> sln[{:?}] == {:?} (!= Unassigned? {:?}) ",
                         x, sln[x], sln[x] != Unassigned);
                sln[x] != Unassigned
            }));

            assert!((1..8).all(|x| sln[x] != Unassigned),
                    "Expected all values to be assigned, got {:?} instead",
                    sln);

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
            panic!("Expression contains a contradiction, so shouldn't succeed.")
        }
    }
}

#[derive(PartialEq, Eq, Debug, Clone)]
enum ClauseAnalysis {
    IsTrue, IsFalse, IsUnit (Term), IsIndeterminate
}

/**
 */
fn analyse_clause(clause: &[Term], sln: &Solution) -> ClauseAnalysis {
    let mut value = False;
    let mut unassigned_terms = Vec::with_capacity(clause.len());

    // walk each term in the Clause and try to evaluate it.
    for term in clause.iter() {
        let t = term.value(sln);

        if t == Unassigned {
            unassigned_terms.push(term);
        }

        value = value | t;
        if value == True {
            break;
        }
    }

    match value {
        True => ClauseAnalysis::IsTrue,
        False => ClauseAnalysis::IsFalse,
        Conflict => {
            panic!("Encountered conflict during clause analysis!");
        },
        Unassigned => {
            assert!(unassigned_terms.len() > 0);

            if unassigned_terms.len() == 1 {
                ClauseAnalysis::IsUnit(unassigned_terms[0].clone())
            }
            else {
                ClauseAnalysis::IsIndeterminate
            }
        }
    }
}

#[test]
fn analysis_detects_single_term_unit_clause() {
    let sln = Solution::new(4);
    let rval = analyse_clause(&[Lit(1)], &sln);
    assert!(rval == ClauseAnalysis::IsUnit(Lit(1)));
}

#[test]
fn analysis_detects_unit_clause() {
    let sln = Solution::from(4, &[(1, False), (2, False), (4, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsUnit(Lit(3)));
}

#[test]
fn analysis_detects_true_clause() {
    let sln = Solution::from(4, &[(3, True)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsTrue);
}

#[test]
fn analysis_detects_false_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(2), Lit(3)], &sln);
    assert!(rval == ClauseAnalysis::IsFalse);
}


#[test]
fn analysis_detects_indeterminate_clause() {
    let sln = Solution::from(4, &[(2, False), (3, False)]);
    let rval = analyse_clause(&[Lit(1), Lit(2), Lit(3), Lit(4)], &sln);
    assert!(rval == ClauseAnalysis::IsIndeterminate);
}

#[derive(Debug)]
enum PropagationResult {
    EvaluatesToFalse,

    /**
     * Contradiction detected during propagation.
     */
    Contradiction (Var),

    /**
     * The propagation succeded,
     */
    Success
}

impl PropagationResult {
    fn is_success(&self) -> bool {
        match *self {
            PropagationResult::Success => true,
            _ => false
        }
    }

    fn is_failure(&self) -> bool {
        !self.is_success()
    }
}

static mut dump_idx : usize = 0;

unsafe fn get_dump_idx() -> usize {
    let r = dump_idx;
    dump_idx = dump_idx + 1;
    r
}

fn deduce_value(t: Term) -> SolutionValue {
    match t {
        Lit (_) => True,
        Not (_) => False
    }
}

fn extract_var_roots(v: Var, c: &[Term], sln: &Solution) -> Vec<(Var, SolutionValue)> {
    let mut rval = Vec::with_capacity(c.len()-1);
    for t in c.iter() {
        let tv = t.var();
        if tv != v { rval.push((tv, sln[tv])); }
    }
    rval
}

/**
 * Propagates the logical consequences of the current solution.
 */
fn propagate(level: usize,
             seed_var: Var,
             seed_val: SolutionValue,
             state: &mut SolveState,
             exp: &Expression) -> PropagationResult
{
    let mut queue : Vec<Var> = Vec::new();
    let mut deduced : VecMap<Var, SolutionValue> = VecMap::new();

    queue.push(seed_var);
    deduced.insert(seed_var, seed_val);
    state.implications.insert(level, seed_var, seed_val, &[]);

    while !queue.is_empty() {
        let implied_var = queue.pop().unwrap();
        let implied_val = *deduced.get(&implied_var).unwrap();
        state.solution[implied_var] = implied_val;

        println!("\tChecking implications of setting {:?} = {:?}",
            implied_var, implied_val);

        for clause in exp.clauses_containing(implied_var) {
            match analyse_clause(clause, &state.solution) {
                ClauseAnalysis::IsUnit (term) => {
                    println!("\t\tFound unit clause {:?}, term of interest is {:?}", clause, term);
                    let var = term.var();
                    let deduced_value = deduce_value(term);

                    println!("\t\tDeduced that {:?} = {:?}", var, deduced_value);
                    let roots = extract_var_roots(var, clause, &state.solution);

                    // Do we have any previouly-deduced values for the thing we
                    // just decided on?
                    match *(deduced.get(&var).unwrap_or(&Unassigned)) {
                        // no? good! record our deduction and queue the variable for later
                        // processing
                        Unassigned => {
                            state.implications.insert(level, var, deduced_value, &roots[..]);
                            state.brancher.remove(var);
                            deduced.insert(var, deduced_value);
                            queue.push(var);
                        },

                        // yes, but it contradicts what we have just deduced
                        x if (x != deduced_value) => {
                            debug!("\t\tDetected contradiction on {:?}!", var);
                            state.implications.insert(level, var, deduced_value, &roots[..]);
                            state.solution[var] = Conflict;

                            // unsafe {
                            //     let filename = format!("{:016x}.dot", get_dump_idx());
                            //     debug!("Dumping graph to: {:?}", filename);
                            //     dump_graph(&filename, &state.implications);
                            // }

                            return PropagationResult::Contradiction(var)
                        },

                        // yes, and it agrees with what we deduced just now
                        _ => {}
                    }
                },

                ClauseAnalysis::IsFalse => {
                    // oh, dear. All variables in the term have values and the
                    // clause evaluates to false. Bail out and let the caller
                    // know that this can't possibly be the right answer.
                    debug!("\t\tEvaluates to false");
                    return PropagationResult::EvaluatesToFalse
                },

                _ => {}
            }
        }
    }
    PropagationResult::Success
}

#[test]
fn propagation_deduces_true_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Lit(3), Lit(4)]]);

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(4),
        solution: Solution::from(4, &[(1, False), (2, False)]),
        stack: DecisionStack::new(),
        implications: ImplicationGraph::from(&[
            (1, (1, False), &[]),
            (2, (2, False), &[])
        ]),
    };

    state.brancher.remove_all(&[1, 2, 4]);

    match propagate(1, 4, False, &mut state, &exp) {
        PropagationResult::Success => {
            assert_eq!(state.solution[3], True);
            assert_eq!(state.solution[4], False);
            assert_eq!(state.implications.len(), 4);
            assert!(!state.has_unassigned_vars());
        },
        other => {
            panic!("Unexpected propagation result: {:?}", other)
        }
    }
}

#[test]
fn propagation_deduces_false_value() {
    let exp = Expression::from(&[&[Lit(1), Lit(2), Not(3), Lit(4)]]);

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(4),
        implications: ImplicationGraph::from(&[
            (1, (1, False), &[]),
            (2, (2, False), &[])
        ]),
        solution: Solution::from(4, &[(1, False), (2, False)]),
        stack: DecisionStack::new()
    };

    state.brancher.remove_all(&[1, 2, 4]);

    match propagate(3, 4, False, &mut state, &exp) {
        PropagationResult::Success => {
            assert_eq!(state.solution[4], False);
            assert_eq!(state.implications.len(), 4);
            assert!(!state.has_unassigned_vars());
        },
        other => {
            panic!("Unexpected propagation result: {:?}", other)
        }
    }
}

#[test]
fn propagation_detects_contradictions() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(3)]
    ]);

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(4),
        implications: ImplicationGraph::from(&[(1, (1, False), &[])]),
        solution: Solution::from(3, &[(1, False)]),
        stack: DecisionStack::new()
    };

    match propagate(1, 2, False, &mut state, &exp) {
        PropagationResult::Contradiction (3) => {
            // assert that the side-effects on the solver state are what we
            // expect
            assert_eq!(state.solution[2], False);
            assert_eq!(state.solution[3], Conflict);

            // len 4 (1 each for 1 & 2, plus one each for the true and false
            // values on the conflict
            assert_eq!(4, state.implications.len());
        },
        other => panic!("Unexpected result from propagate(): {:?}", other)
    }
}

#[test]
fn propagation_detects_evaluation_to_false() {
    let exp = Expression::from(&[
        &[Lit(1), Lit(2), Lit(3)],
        &[Lit(1), Lit(2), Not(4)],
    ]);

    let mut state = SolveState {
        brancher: &mut NaiveBrancher::new(4),
        implications: ImplicationGraph::from(&[
            (1, (1, False), &[]),
            (2, (2, False), &[])
        ]),
        solution: Solution::from(4, &[(1, False), (2, False)]),
        stack: DecisionStack::new()
    };

    match propagate(1, 3, False, &mut state, &exp) {
        PropagationResult::EvaluatesToFalse => {
            assert_eq!(state.solution[3], False);
            assert_eq!(state.solution[4], Unassigned);
            assert_eq!(state.implications.len(), 3);
            for x in (1..3) {
                assert!(state.implications.has(x));
            }
        },
        other => panic!("Unexpected result from propagate(): {:?}", other)
    }
}
