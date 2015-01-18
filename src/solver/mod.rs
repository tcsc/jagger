pub use self::types::{Expression, Clause, Term, Solution, SolutionValue, Var};
pub use self::solver::{solve};

pub mod types;
pub mod solver;
mod benchmarks;