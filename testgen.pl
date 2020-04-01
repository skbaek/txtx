#!/usr/bin/env swipl

:- initialization(main, main).
:- use_module(library(shell)).
% :- [solve, prove, check].

path_cat_id(Path, Cat, ID) :- 
  atom_codes(Path, Codes0), 
  append(_, [47 | Codes1], Codes0),
  \+ member(47, Codes1), 
  append([C0, C1, C2 | Rest], [46, 112], Codes1),
  string_codes(Cat, [C0, C1, C2]),
  string_codes(ID, Rest).

dir_files(Dir, Entries) :- 
  directory_files(Dir, TempA), 
  delete(TempA, '.', TempB),
  delete(TempB, '..', Entries).

rec_path_files(Path, [Path]) :- 
  exists_file(Path). 

rec_path_files(Path, Files) :- 
  exists_directory(Path), 
  rec_dir_files(Path, Files).

rec_dir_files(Dir, Files) :- 
  dir_files(Dir, Entries), 
  maplist(directory_file_path(Dir), Entries, Paths),
  maplist(rec_path_files, Paths, Filess),
  append(Filess, Files).

msg(PTRN, ARGS) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  format(PTRN, ARGS),
  write("\n\n").

msg(STR) :-
  % write(" ────────────────────────────────────────────────────────────────── "), 
  write("                                                                      > "), 
  write(STR),
  write("\n\n").

is_fol_thm(PATH) :- 
  string_concat(_, ".p", PATH),
  \+ sub_string(PATH, _, _, _, "="),
  \+ sub_string(PATH, _, _, _, "^"), 
  \+ sub_string(PATH, _, _, _, "_"), 
  is_thm(PATH).
  % file_strings(PATH, STRS),
  % member(STR, STRS),
  % split_string(STR, ":", " %", ["Status", STAT_STR]), 
  % member(STAT_STR, ["Theorem", "Unsatisfiable"]).
  
call_tptp2x(PATH) :- 
  path_cat_id(PATH, CAT, ID), 
  atomics_to_string([CAT, ID, ".tptp"], TPTP),
  atomics_to_string(["tptp2X -ftptp -dtemp ~/programs/TPTP/Problems/", CAT, "/", CAT, ID, ".p"], CMD), 
  shell(CMD, _),
  atomics_to_string(["temp/", CAT, "/", TPTP], OLD_PATH),
  atomics_to_string(["p/", TPTP], NEW_PATH),
  mv(OLD_PATH, NEW_PATH),
  shell("rm -r temp", _).

mv_concat(FILE, LIST) :- 
  atomic_list_concat(LIST, PATH),
  mv(FILE, PATH).

stream_strings(STRM, STRS) :-
  read_line_to_string(STRM, STR), 
  (
    STR = end_of_file -> 
    STRS = [] 
  ;
    STRS = [STR | REST],
    stream_strings(STRM, REST)
  ).

is_thm_core(STRM) :-
  read_line_to_string(STRM, STR), 
  (
    STR = end_of_file -> 
    close(STRM), 
    false
  ;
    (
      split_string(STR, ":", " %", ["Status", STAT]), 
      member(STAT, ["Theorem", "Unsatisfiable"])
    ) -> 
    close(STRM)
  ;
    is_thm_core(STRM)
  ).

is_thm(PATH) :-
  open(PATH, read, STRM), 
  is_thm_core(STRM).

file_strings(FILE, STRS) :-
  open(FILE, read, STRM), 
  stream_strings(STRM, STRS), 
  close(STRM).

prob_ext(PATH) :- 
  call_tptp2x(PATH) -> true ;
  atomics_to_string(["echo ", PATH, " >> ", "failed.txt"], CMD),
  shell(CMD, _).

drop(0, X, X).
drop(NUM, [_ | Y], Z) :-
  0 < NUM,
  PRED is NUM - 1,  
  drop(PRED, Y, Z).
  
include_cut(_, [], []). 
include_cut(PRED, [ELEM | LIST_I], LIST_O) :- 
  call(PRED, ELEM) -> 
  LIST_O = [ELEM | LIST_T], 
  include_cut(PRED, LIST_I, LIST_T) 
; 
  include_cut(PRED, LIST_I, LIST_O). 

main :- 
  set_prolog_flag(stack_limit, 4_294_967_296),
  msg("Generating paths"),
  rec_dir_files("/home/sk/programs/TPTP/Problems", ALL), 
  include_cut(is_fol_thm, ALL, PATHS), !, 
  % append(_, ['/home/sk/programs/TPTP/Problems/CSR/CSR061+6.p' | REST], TEMP),
  % PATHS = (['/home/sk/programs/TPTP/Problems/CSR/CSR061+6.p' | REST]),
  maplist_cut(prob_ext, PATHS).
  
  % atom_number(NUM_ATOM, NUM),
  % msg("Enter bench loop"),
  % gen_loop(PROVER, NUM, PATHS), 
  % msg("Exit bench loop").

maplist_try(_, []).
maplist_try(GOAL, [ELEM | LIST]) :- 
  call(GOAL, ELEM) -> 
  maplist_try(GOAL, LIST)
; 
  maplist_try(GOAL, LIST).

maplist_cut(_, []).
maplist_cut(GOAL, [Elem | List]) :- 
  call(GOAL, Elem), !, 
  maplist_cut(GOAL, List). 

write_list([]).
write_list([Elem | List]) :- 
  format('~w\n', Elem),
  write_list(List).