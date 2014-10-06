#![feature(phase)]
#[phase(plugin, link)] extern crate log;

mod metadata;
mod pkg;
mod solver;
mod formulator;

#[cfg(not(test))]
fn main() {

}