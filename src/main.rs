#![feature(box_syntax)]
#![allow(unstable)]
#![allow(dead_code)]
#![feature(old_io)]
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
//	env_logger::init().unwrap();
}