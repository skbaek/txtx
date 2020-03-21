#!/usr/bin/env swipl

:- initialization(main, main).
:- use_module(library(shell)).
:- [basic].

passed(PATH) :- 
  string_concat("ps", _, PATH).

main([NUM_ATOM]) :- 
  atom_number(NUM_ATOM, NUM),
  directory_files("vp", X),
  include(passed, X, Y),
  random_plucks(NUM, Y, Z, _),
  write_list_file("/home/sk/problist", Z).
