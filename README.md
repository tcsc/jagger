jagger
======

An experiment in package management using a SAT solver, written in Rust.

Why?
====

I was contributing patches to a package management system that was having trouble 
resolving some package dependencies - which is kind of a big deal for a package 
management system. Anyway, the brute-force O(n^2) way I solved it seemed decidedly 
inelegant, and a workmate suggested looking at SAT solvers. Since I apparently missed 
SAT solvers in my university days, I thought it would be fun to give it a try myself. 

I was also after a small project to use to learn Rust, and this just happened to crop 
up at the same time. Why Rust? Because it looks like someone read my mind, made a list 
of all my favourite featues in all my favourite languages, and then sat down to try and 
make a language around them. That's why.

Why is it called "Jagger"?
==========================

It's a SATISFIABILITY solver. It's after SATISFACTION. Often it can't get any. Do I
need to draw a picture? 

Caveat
======

This will probably never be finished. If you're after something actually functional, 
you're much better off looking at [SUSE's libsolv project](https://github.com/openSUSE/libsolv). 
People that actually know what they're doing are working on that, as opposed to the 
half-arsed amatuer hour over here.
