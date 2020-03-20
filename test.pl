:- [basic].

print_list_size(LIST) :-
  length(LIST, NUM), 
  write(NUM), 
  write(" ").

print_bilist_size((LFT, RGT)) :-
  length(LFT, NUM_L), 
  length(RGT, NUM_R), 
  write(NUM_L), 
  write(" "),
  write(NUM_R), 
  write(" ").

bilist_size((LFT, RGT), NUM_L, NUM_R) :-
  length(LFT, NUM_L), 
  length(RGT, NUM_R).

test_list(NUM) :- 
  range(0, NUM, NUMS), 
  (
    pluck(NUMS, ELEM, REST),
    length(REST, _),
    ELEM = NUM
  ).

test_bilist(NUM) :- 
  range(0, NUM, NUMS), 
  (
    pick((NUMS, []), ELEM, REST),
    bilist_size(REST, _, _),
    ELEM = NUM
  ).