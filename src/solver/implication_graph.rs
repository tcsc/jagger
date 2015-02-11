use std::collections;
use std::collections::{HashMap, BTreeMap, RingBuf};
use std::iter::FromIterator;
use std::borrow::Cow;
use log;

use graphviz as dot;

use solver::types;
use solver::types::{Solution, Expression, Var, VarSet, Clause};
use solver::types::Term::{self, Lit, Not};
use solver::types::SolutionValue::{self, True, False, Unassigned};
use collections::VecSet;

// ----------------------------------------------------------------------------
// Implication graph implementation
// ----------------------------------------------------------------------------

// {a=1} => {level: 1, roots: []} <--+
//                                    \
//      {b=1} => {level: 1, roots: {a:1}} <---+
//                                             \
//                                            {e=0} => {level: 3, roots [{b=1}, {c=1}, {d=1}]}
//                                            / /
// {c=0} => {level: 2, roots:[]} <-----------+ /
//                                            /
// {d=1} => {level: 3, roots:[]} <-----------+

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Show)]
struct Assignment(Var, SolutionValue);

/**
 * An abbreviated assignment (ha!), useful for consructing assignment literals
 * when writing tests. 
 */
type Asmt = (Var, SolutionValue);

impl Assignment {
    fn new(var: Var, val: SolutionValue) -> Assignment {
        Assignment(var, val)
    }

    fn from(a: Asmt) -> Assignment {
        let (var, val) = a;
        Assignment::new(var, val)
    }
}

type Assignments = Vec<Assignment>;


// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

#[derive(Show)]
struct Implication {
	level: usize,
	roots: Vec<Assignment>
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

type GraphImpl = HashMap<Assignment, Implication>;


#[derive(Show)]
pub struct ImplicationGraph {
    map: GraphImpl
}

impl ImplicationGraph {
    pub fn new() -> ImplicationGraph {
        ImplicationGraph { map: HashMap::new() }
    }

    pub fn from(items: &[(usize, Asmt, &[Asmt] )]) -> ImplicationGraph {
        let mut result = ImplicationGraph::new();
        for &(level, asmt, roots) in items.iter() {
            let (var, val) = asmt;
            result.insert(level, var, val, roots);
        }
        result
    }

    pub fn insert(&mut self,
    	          level: usize, 
    	          var: Var, 
    	          val: SolutionValue, 
    			  roots: &[Asmt]) 
    {
    	self.map.insert(
    		Assignment(var, val), 
    		Implication { 
    			level: level, 
    			roots: roots.iter()
                            .map(mk_assignment)
                            .collect()
    		});
    }

    pub fn remove(&mut self, var: Var, val: SolutionValue) {
    	self.map.remove(&Assignment(var, val));
    } 

    pub fn learn_conflict_clause(&self, conflict: Var, decision: Asmt) -> Clause {
        dump_graph("learn_conflict.dot", self);
        learn_conflict_clause(&self.map, conflict, mk_assignment(&decision))
    }

    /**
     * Does this graph have an implication for the given variable.
     */
    pub fn has(&self, v: Var) -> bool {
        self.map.get(&Assignment(v, False)).is_some() || 
        self.map.get(&Assignment(v, True)).is_some()
    }

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn mk_assignment(asmt: &Asmt) -> Assignment {
    Assignment(asmt.0, asmt.1)
}

#[config(test)]
fn test_graph() -> ImplicationGraph {
    // graph from 
    // http://www.cs.princeton.edu/courses/archive/fall13/cos402/readings/SAT_learning_clauses.pdf
    // Section 4: Learning Schemes
    ImplicationGraph::from(&[
        (1, (7, False), &[]),
        (2, (8, False), &[]),
        (3, (9, False), &[]),
        (4, (1, False), &[]),
        (4, (2, True),  &[(1, False)]),
        (4, (3, True),  &[(1, False), (7, False)]),
        (4, (4, True),  &[(2, True),  (3, True)]),
        (4, (5, True),  &[(8, False), (4, True)]),
        (4, (6, True),  &[(9, False), (4, True)]),
        (4, (5, False), &[(6, True)])
    ])   
}

#[test]
fn new_graphs_are_empty() {
    let g = ImplicationGraph::new();
    assert!(g.is_empty());
    assert_eq!(g.len(), 0);
}

#[test]
fn adding_new_node_increases_length() {
    let mut g = ImplicationGraph::new();
    g.insert(1, 42, False, &[]);
    assert!(!g.is_empty());
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn learn_conflict_clause(g: &GraphImpl, v: Var, decision: Assignment) -> Clause {
    let level = g.get(&decision).unwrap().level;

    let negative_assignment = Assignment(v, False);
    let negative_path = find_path(g, negative_assignment, decision).unwrap();

    let positive_assignment = Assignment(v, True);
    let positive_path = find_path(g, positive_assignment, decision).unwrap();
    
    let uip = find_first_uip(g, level, &negative_path, &positive_path);

    // ok, so now we have a point we can cut at. We now need to find all of the 
    // edges in the graph that cross the cut. For example, given the graph 
    // (where the cut is marked with an asterisk)
    //
    //            8  
    //              \
    //       2        5+
    //     /   \    / 
    //   1       4 *      5-
    //     \   /    \   / 
    //       3        6 
    //     /        /
    //   7        9
    //
    // ...the nodes 5+, 5- & 6 are on one side of the cut, and everything else is 
    // on the other. The nodes on with edges that cross the cut (4, 8 & 9) are 
    // the ones we're interested in.
    //
    // We know the path from both 5+ and 5- to 4, so we can assume that any 
    // nodes are on those paths are on the conflict side, so we can simply walk
    // the graph from 5+/- backwards. If we hit a node that is not in the 
    // conflict side, we add that to the learned conflict clause.

    // NB  - make some sort of generic BFS.
    let conflict_side_vars = mk_conflict_set(&negative_path, &positive_path, uip);
    let mut conflict_clause : VecSet<Term> = VecSet::new();
    for v in conflict_side_vars.iter() {
        let i = g.get(v).unwrap();
        for r in i.roots.iter() {
            if !conflict_side_vars.contains(r) {
                let t =  match *r {
                    Assignment(var, True) => Not(var),
                    Assignment(var, False) => Lit(var),
                    _ => panic!("This should never happen")
                };
                conflict_clause.insert(t);
            }
        }
    }

    FromIterator::from_iter(
        conflict_clause.iter().map(|&x| x))
}

#[test]
fn learn_clause_finds_expected_clause_from_wikipedia_example() {

    let g = ImplicationGraph::from(&[
        (1, ( 1, False), &[]),
        (1, ( 4, True),  &[(1, False)]),
        (2, ( 3, True),  &[]),
        (2, ( 8, False), &[(1, False), (3, True)]),
        (3, ( 2, False), &[]),
        (3, (11, True),  &[(2, False)]),
        (4, ( 7, True),  &[]),
        (4, ( 9, True),  &[(3, True), (7, True)]),
        (4, ( 9, False), &[(7, True), (8, False)]),
    ]);

    let clause = learn_conflict_clause(&g.map, 9, Assignment::new(7, True));
    assert!(clause.len() == 3);
    assert!(clause.iter().any(|t| *t == Not(3)), "Clause must contain ~3");
    assert!(clause.iter().any(|t| *t == Not(7)), "Clause must contain ~7");
    assert!(clause.iter().any(|t| *t == Lit(8)), "Clause must contain 8");
}

#[test]
fn learn_clause_finds_expected_clause_from_princeton_example() {

    let g = test_graph();

    let clause = learn_conflict_clause(&g.map, 5, Assignment::new(1, False));
    assert_eq!(3, clause.len());
    assert!(clause.iter().any(|t| *t == Not(4)), "Clause must contain ~4");
    assert!(clause.iter().any(|t| *t == Lit(8)), "Clause must contain 8");
    assert!(clause.iter().any(|t| *t == Lit(9)), "Clause must contain 9");    
}

fn mk_conflict_set(a: &Assignments, b: &Assignments, uip: Assignment) -> VecSet<Assignment> {
    let mut result = VecSet::new();
    result.extend(a.iter().take_while(|&x| *x != uip).map(|&x| x));
    result.extend(b.iter().take_while(|&x| *x != uip).map(|&x| x));
    result
}

#[test]
fn mk_conflict_set_doesnt_include_uip() {
    let path_a = mk_assignments(&[(5,True), (4,True), (2,True), (1, False)]);
    let path_b = mk_assignments(&[(5,False), (6, True), (4,True), (3,True), (1, False)]);
    let uip = Assignment(4, True);
    let conflict_set = mk_conflict_set(&path_a, &path_b, uip);
    let expected : VecSet<Assignment> = FromIterator::from_iter(
        mk_assignments(&[(5, True), (5, False), (6, True)])
            .iter()
            .map(|&x| x)
    ); 

    assert!(conflict_set == expected);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn find_first_uip(g: &GraphImpl,
                  level: usize,
                  negative_path: &Assignments, 
                  positive_path: &Assignments) -> Assignment {
    for asmt in negative_path.iter() {
        let l = g.get(asmt).unwrap().level;
        if level != l { continue; }
        match positive_path.iter().find(|&x| x == asmt) {
            None => {},
            Some(_) => { return *asmt }
        }
    }

    panic!("No UIP found");
}

#[test]
fn find_first_uip_picks_correct_point() {
    let g = test_graph();
    let decision = Assignment(1, False);
    let negative_path = find_path(&g.map, Assignment(5, False), decision).unwrap();
    let positive_path = find_path(&g.map, Assignment(5, True), decision).unwrap();
    let Assignment(var, val) = find_first_uip(&g.map, 4, &negative_path, &positive_path);
    assert_eq!(4, var);
    assert_eq!(True, val);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * Finds a path through an implication graph, from a given source to a given 
 * destination. Should find the shortest available path.
 */
fn find_path(g: &GraphImpl, src: Assignment, dst: Assignment) -> Option<Assignments> {
    let mut result : Assignments = Vec::new();
    let mut visited : VecSet<Assignment> = VecSet::new();
    let mut queue : RingBuf<(Assignment, Assignments)> = RingBuf::new();
    queue.push_back((src, vec!(src)));

    while !queue.is_empty() {
        let (parent, path_to_parent) = queue.pop_front().unwrap();

        if !visited.insert(parent) { 
            continue; 
        }

        match g.get(&parent) {
            None => {},
            Some(ref i) => {
                for child in i.roots.iter().map(|&x| x) {
                    let mut path = path_to_parent.clone();
                    path.push(child);
                    if dst == child {
                        return Some(path)
                    }
                    queue.push_back((child, path));
                }
            }
        }
    }

    return None
}

#[config(test)]
fn mk_assignments(asmts: &[Asmt]) -> Assignments {
    asmts.iter()
         .map(|&(var, val)| Assignment(var, val))
         .collect()
}

#[test]
fn find_path_finds_expected_path() {
    let g = test_graph();
    let path = find_path(&g.map, Assignment(5, True), Assignment(1, False)).unwrap();
    let path_a = mk_assignments(&[(5,True), (4,True), (2,True), (1, False)]);
    let path_b = mk_assignments(&[(5,True), (4,True), (3,True), (1, False)]);
    assert!((path_a == path) || (path_b == path));
}

#[test]
fn find_path_finds_shortest_path() {
    //  /-- 1 --- 2 --- 5 --\
    // 0                     6
    //  \-- 3 --------- 4 --/
    //
    let mut g = ImplicationGraph::from(&[
        (1, (0, False), &[]),
        (1, (1, False), &[(0, False)]),
        (1, (2, False), &[(1, False)]),
        (1, (5, False), &[(2, False)]),
        (1, (3, False), &[(0, False)]),
        (1, (4, False), &[(3, False)]),
        (1, (6, False), &[(4, False), (5,False)])
    ]);
    
    //dump_graph("shortest.dot", &g);

    let path = find_path(&g.map, Assignment(6, False), Assignment(0, False)).unwrap();
    let expected = mk_assignments(&[(6, False), (4, False), (3, False), (0, False)]);
    assert!(path == expected);
}


// ----------------------------------------------------------------------------
// Debugging tools
// ----------------------------------------------------------------------------

pub type Node = Assignment;
pub type Edge = (Node, Node);

impl<'a> dot::Labeller<'a, Node, Edge> for ImplicationGraph {
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("Implications").unwrap()
    }

    fn node_id(&'a self, n: &Node) -> dot::Id<'a> {
        let &Assignment(var, val) = n;
        let id = format!("N{:?}_{:?}", var, val);
        dot::Id::new(id).unwrap()
    }

    fn node_label<'b>(&'a self, n: &Node) -> dot::LabelText<'b> {
        let i = self.map.get(n).unwrap();
        let &Assignment(var, val) = n;
        let label = format!("{} = {:?} @ Level {}", var, val, i.level);
        dot::LabelText::LabelStr(Cow::Owned(label))
    }
}

impl<'a> dot::GraphWalk<'a, Node, Edge> for ImplicationGraph {
    fn nodes(&self) -> dot::Nodes<'a, Node> {
        let mut nodes = Vec::with_capacity(self.len());
        for a in self.map.keys() {
            nodes.push(a.clone());
        }
        Cow::Owned(nodes)
    }

    fn edges(&self) -> dot::Edges<'a, Edge> {
        let mut edges = Vec::new();
        for (asmt, implication) in self.map.iter() {
            for root in implication.roots.iter() {
                edges.push((root.clone(), asmt.clone()))            
            }
        }
        Cow::Owned(edges)
    }

    fn source(&self, e: &Edge) -> Node { 
        let &(ref src, _) = e; 
        src.clone() 
    }

    fn target(&self, e: &Edge) -> Node { 
        let &(_, ref dst) = e; 
        dst.clone() 
    }
}

pub fn dump_graph(filename: &str, g: &ImplicationGraph) {
    use std::old_io::File;
    let mut f = File::create(&Path::new(filename));
    dot::render(g, &mut f).unwrap();
}
