#![feature(box_syntax)]
#![allow(unstable)]
#[macro_use] extern crate log;
extern crate graphviz;
extern crate test;

mod collections;
mod metadata;
mod pkg;
mod solver;
mod dimacs;
mod formulator;

#[cfg(not(test))]
fn main() {

}