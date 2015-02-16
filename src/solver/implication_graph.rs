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

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Copy, Debug)]
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

#[derive(Debug, PartialEq, Eq)]
struct Implication {
	level: usize,
	roots: Vec<Assignment>,
    consequences: Vec<Assignment>
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

type GraphImpl = HashMap<Assignment, Implication>;

/**
 * \todo Derive a more cache-friendly representation of the implication graph
 *       that will still let us represent two separate implication trees for a
 *       conflict. (Using an array indexed by the variable won't do that, but
 *       the real answer shoudl lie somewhere along that path).
 */
#[derive(Debug, PartialEq, Eq)]
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

    /**
     * \pre All roots must exist in the graph.
     */
    pub fn insert(&mut self,
    	          level: usize,
    	          var: Var,
    	          val: SolutionValue,
    			  roots: &[Asmt])
    {
        let asmt = Assignment(var, val);
        let mut rs = Vec::with_capacity(roots.len());

        for &(rvar, rval) in roots {
            let root = Assignment(rvar, rval);
            rs.push(root);
            self.map.get_mut(&root).unwrap()
                    .consequences.push(asmt);
        }

        let implication = Implication {
            level: level,
            roots: rs,
            consequences: Vec::new()
        };

        match self.map.insert(asmt, implication) {
            None => {},
            Some(_) => {
                panic!("Assignment for {:?} already exists!", asmt);
                // note that we have already screwed the graph by adding the new
                // assignment to other nodes' consequences list at this point.
            }
        }
    }

    /**
     * Strips an assignment and all of its recursive consequences from the
     * implication graph. Returns a list of all the variables removed from
     * the graph.
     */
    pub fn strip(&mut self, var: Var, val: SolutionValue) -> Vec<Var> {
        let mut queue = vec!(Assignment(var, val));
        let mut result = Vec::new();

        // while we still have assignments to check...
        while !queue.is_empty() {
            let a = queue.pop().unwrap();

            match self.map.remove(&a) {
                None => {},
                Some(implication) => {
                    // add the consequences of this assignment to the queue of
                    // nodes to remove
                    queue.push_all(implication.consequences.as_slice());

                    // remove this assignment from our roots' consequences
                    for r in implication.roots.iter() {
                        match self.map.get_mut(r) {
                            Some(root) => {
                                root.consequences.retain(|&x| x != a);
                            },
                            None => {}
                        }
                    }
                }
            }
        }
        result
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

#[test]
fn inserting_nodes_updates_consequences_and_roots() {
    let g = test_graph();
    let key = Assignment(3, True);
    let i = g.map.get(&key).unwrap();

    // assert that the new key has the roots we expect
    println!("Checking that {:?} appears in {:?}", Assignment(1, False), i.roots);
    i.roots.iter().find(|&x| *x == Assignment(1, False)).unwrap();

    println!("Checking that {:?} appears in {:?}", Assignment(7, False), i.roots);
    i.roots.iter().find(|&x| *x == Assignment(7, False)).unwrap();

    // assert that the new key appears in it's roots consequences
    println!("Checking that {:?} appears in the consequences of {:?}",
        key, Assignment(1, False));
    assert!(g.map.get(&Assignment(1, False)).unwrap()
                 .consequences.iter()
                 .find(|&x| *x == key)
                 .is_some());

    println!("Checking that {:?} appears in the consequences of {:?}",
        key, Assignment(7, False));
    assert!(g.map.get(&Assignment(7, False)).unwrap()
                 .consequences.iter()
                 .find(|&x| *x == key)
                 .is_some());
}

#[test]
fn removing_nodes_updates_consequences_of_roots() {
    let mut g = test_graph();
    let key = Assignment(3, True);
    let i = g.strip(4, True);

    // pre-strip 4+
    //            8
    //              \
    //       2        5+
    //     /   \    /
    //   1       4 *      5-
    //     \   /    \   /
    //       3        6
    //     /        /
    //   7        9

    // post-strip
    //            8
    //       2
    //     /
    //   1
    //     \
    //       3
    //     /
    //   7        9

    let expected = ImplicationGraph::from(&[
        (1, (7, False), &[]),
        (2, (8, False), &[]),
        (3, (9, False), &[]),
        (4, (1, False), &[]),
        (4, (2, True),  &[(1, False)]),
        (4, (3, True),  &[(1, False), (7, False)])
    ]);

    dump_graph("remove_expected.dot", &expected);
    dump_graph("remove_actual.dot", &g);


    assert!(g == expected);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

fn learn_conflict_clause(g: &GraphImpl, v: Var, decision: Assignment) -> Clause {
    let level = g.get(&decision).unwrap().level;

    let negative_assignment = Assignment(v, False);
    let negative_paths = find_paths(g, negative_assignment, decision);

    let positive_assignment = Assignment(v, True);
    let positive_paths = find_paths(g, positive_assignment, decision);

    let uip = find_first_uip(g, level, &negative_paths[0], &positive_paths[0]);

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
    let conflict_side_vars = mk_conflict_set(&negative_paths, &positive_paths, uip);
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

/**
 * Collects the set of nodes in the conflict side of the cut.
 */
fn mk_conflict_set(a: &Vec<Assignments>,
                   b: &Vec<Assignments>,
                   uip: Assignment) -> VecSet<Assignment> {
    let mut result = VecSet::new();
    for v in a.iter().chain(b.iter()) {
        result.extend(v.iter().take_while(|&x| *x != uip).map(|&x| x));
    }
    result
}

#[test]
fn learned_clause_considers_all_nodes_in_conflict_side() {
    //       13
    //         \
    //    12   14      15
    //     |   /         \
    //    11  *3 - *8 - *~7
    //     | /
    // 1 - 2 - 5 - 6 - *7
    //       \         /
    //        +- *4 -+
    //           /
    //     10 - 9

    // The conflict side contains any path from +/~7 back to the first uip at
    // 2, and so the resulting learned clause should include 2, 9, 15 and
    // nothing else.
    let g = ImplicationGraph::from(&[
        (1, ( 1, False), &[]),
        (1, (10, False), &[]),
        (1, (13, False), &[]),
        (1, (15, False), &[]),
        (1, ( 2, False), &[(1, False)]),
        (1, (11, False), &[(2, False)]),
        (1, (12, False), &[(11, False)]),
        (1, ( 3, False), &[(2, False)]),
        (1, ( 8, False), &[(3, False)]),
        (1, ( 7, False), &[(8, False), (15, False)]),
        (1, (14, False), &[(3,False), (13,False)]),
        (1, ( 9, False), &[(10, False)]),
        (1, ( 4, False), &[(2, False), (9, False)]),
        (1, ( 5, False), &[(2, False)]),
        (1, ( 6, False), &[(5, False)]),
        (1, ( 7, True),  &[(6, False), (4, False)]),
    ]);

    let clause = learn_conflict_clause(&g.map, 7, Assignment::new(1, False));
    assert!(clause.len() == 3);
    assert!(clause.iter().any(|t| *t == Lit(2)), "Clause must contain 2");
    assert!(clause.iter().any(|t| *t == Lit(9)), "Clause must contain 9");
    assert!(clause.iter().any(|t| *t == Lit(15)), "Clause must contain 15");
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

#[test]
fn mk_conflict_set_doesnt_include_uip() {
    let path_a = vec!(mk_assignments(&[(5,True), (4,True), (2,True), (1, False)]));
    let path_b = vec!(mk_assignments(&[(5,False), (6, True), (4,True), (3,True), (1, False)]));
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
    let negative_paths = find_paths(&g.map, Assignment(5, False), decision);
    let positive_paths = find_paths(&g.map, Assignment(5, True), decision);
    let Assignment(var, val) = find_first_uip(&g.map, 4, &negative_paths[0], &positive_paths[0]);
    assert_eq!(4, var);
    assert_eq!(True, val);
}

// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------

/**
 * Finds all paths through an implication graph, from a given source to a given
 * destination. Returns the paths shortest to longest. Returns an empty vector
 * if no paths are found.
 *
 * The graph must be acyclic, or we'll be here all day.
 */
fn find_paths(g: &GraphImpl, src: Assignment, dst: Assignment) -> Vec<Assignments> {
    let mut result : Vec<Assignments> = Vec::new();
    let mut queue : RingBuf<(Assignment, Assignments)> = RingBuf::new();
    queue.push_back((src, vec!(src)));

    while !queue.is_empty() {
        let (parent, path_to_parent) = queue.pop_front().unwrap();

        match g.get(&parent) {
            None => {},
            Some(ref i) => {
                for child in i.roots.iter().map(|&x| x) {
                    let mut path = path_to_parent.clone();
                    path.push(child);
                    if dst == child {
                        result.push(path)
                    }
                    else {
                        queue.push_back((child, path));
                    }
                }
            }
        }
    }

    return result
}

#[config(test)]
fn mk_assignments(asmts: &[Asmt]) -> Assignments {
    asmts.iter()
         .map(|&(var, val)| Assignment(var, val))
         .collect()
}

#[test]
fn find_path_finds_all_paths() {
    //  /-- 1 --- 2 --- 5 --\
    // 0             \       6
    //  \-- 3 --------- 4 --/
    //
    let mut g = ImplicationGraph::from(&[
        (1, (0, False), &[]),
        (1, (1, False), &[(0, False)]),
        (1, (2, False), &[(1, False)]),
        (1, (5, False), &[(2, False)]),
        (1, (3, False), &[(0, False)]),
        (1, (4, False), &[(3, False), (2, False)]),
        (1, (6, False), &[(4, False), (5,False)])
    ]);

    let paths = find_paths(&g.map, Assignment(6, False), Assignment(0, False));
    assert_eq!(3, paths.len());
}

#[test]
fn find_paths_finds_shortest_path_first() {
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

    let paths = find_paths(&g.map, Assignment(6, False), Assignment(0, False));
    let expected = mk_assignments(&[(6, False), (4, False), (3, False), (0, False)]);
    assert_eq!(2, paths.len());
    assert!(paths[0] <= paths[1]);
    assert!(paths[0] == expected);
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
