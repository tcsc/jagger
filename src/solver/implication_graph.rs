use std::collections;
use std::collections::{HashMap, BTreeMap};
use std::iter::FromIterator;
use std::borrow::Cow;

use graphviz as dot;

use solver::types;
use solver::types::{Solution, Expression, Var, VarSet};
use solver::types::Term::{self, Lit, Not};
use solver::types::SolutionValue::{self, True, False, Unassigned};


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

#[derive(PartialEq, Eq, PartialOrd, Ord, Hash, Clone, Show)]
struct Assignment {
	var: Var,
	val: SolutionValue
}

struct Implication {
	level: usize,
	roots: Vec<Assignment>
}

pub struct ImplicationGraph {
    map: HashMap<Assignment, Implication>
}

impl ImplicationGraph {
    pub fn new() -> ImplicationGraph {
        ImplicationGraph { map: HashMap::new() }
    }

    pub fn insert(&mut self,
    	          level: usize, 
    	          var: Var, 
    	          val: SolutionValue, 
    			  roots: &[(Var, SolutionValue)]) 
    {
    	self.map.insert(
    		Assignment {var: var, val: val}, 
    		Implication { 
    			level: level, 
    			roots: roots.iter()
    			            .map(mk_assignment)
    			            .collect()
    		});
    }

    pub fn remove(&mut self, var: Var, val: SolutionValue) {
    	self.map.remove(&Assignment {var: var, val: val});
    } 

    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    pub fn len(&self) -> usize {
        self.map.len()
    }
}

fn mk_assignment(asmt: &(Var, SolutionValue)) -> Assignment {
	Assignment { var: asmt.0, val: asmt.1 }
}

#[config(test)]
fn test_graph() -> ImplicationGraph {
    // graph from 
    // http://www.cs.princeton.edu/courses/archive/fall13/cos402/readings/SAT_learning_clauses.pdf
    // Section 4: Learning Schemes
    let mut g = ImplicationGraph::new();
    g.insert(1, 7, False, &[]);
    g.insert(2, 8, False, &[]);
    g.insert(3, 9, False, &[]);
    
    g.insert(4, 1, False, &[]);
    g.insert(4, 2, True,  &[(1, False)]);
    g.insert(4, 3, True,  &[(1, False), (7, False)]);
    g.insert(4, 4, True,  &[(2, True),  (3, True)]);
    g.insert(4, 5, True,  &[(8, False), (4, True)]);
    g.insert(4, 6, True,  &[(9, False), (4, True)]);
    g.insert(4, 5, False, &[(6, True)]);

    g    
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
	assert_eq!(1, g.len());
}

#[test]
fn find_uip() {
    let g = test_graph();
    dump_graph("find_uip.dot", &g);
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
        let id = format!("N{:?}_{:?}", n.var, n.val);
        dot::Id::new(id).unwrap()
    }

    fn node_label<'b>(&'a self, n: &Node) -> dot::LabelText<'b> {
        let i = self.map.get(n).unwrap();
        let label = format!("{} = {:?} @ Level {}", n.var, n.val, i.level);
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

fn dump_graph(filename: &str, g: &ImplicationGraph) {
    use std::io::File;
    let mut f = File::create(&Path::new(filename));
    dot::render(g, &mut f).unwrap();
}
