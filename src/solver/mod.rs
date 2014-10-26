pub use self::types::{Expression, Clause, ClauseRef, Term, Lit, Not, Solution};
pub use self::types::{True, False, Unassigned};
pub use self::solver::{solve};

pub mod types;
pub mod solver;
mod benchmarks;