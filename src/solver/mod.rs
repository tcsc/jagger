pub use self::solver::{Expression, Clause, ClauseRef, Term, Lit, Not, Solution};
pub use self::solver::{True, False, Unassigned};
pub use self::solver::{solve};

pub mod solver;
mod benchmarks;