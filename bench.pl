#!/usr/bin/env swipl

:- initialization(main, main).
:- use_module(library(shell)).
:- [comp_v, comp_m, verify].

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

is_fol_prob(PATH) :- 
  \+ sub_string(PATH, _, _, _, "="),
  \+ sub_string(PATH, _, _, _, "^"), 
  \+ sub_string(PATH, _, _, _, "_"), 
  string_concat(_, ".p", PATH).
  
call_tptp2x(CAT, ID) :- 
  atomics_to_string([CAT, ID, ".tptp"], TPTP),
  atomics_to_string(["tptp2X -ftptp -dtemp ~/programs/TPTP/Problems/", CAT, "/", CAT, ID, ".p"], CMD), 
  shell(CMD, _),
  atomics_to_string(["temp/", CAT, "/", TPTP], TEMP_PATH),
  mv(TEMP_PATH, TPTP),
  shell("rm -r temp", _).

call_compiler(vampire, TPTP, TSTP, TXTX) :- 
  comp_v(TPTP, TSTP, TXTX).

call_compiler(metis, TPTP, TSTP, TXTX) :- 
  comp_m(TPTP, TSTP, TXTX).

call_prover(vampire, TPTP, TSTP) :- 
  atomic_list_concat(["vampire_rel --proof tptp ", TPTP, " > ", TSTP], CMD),  
  shell(CMD, _), 
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  LINE = "% Refutation found. Thanks to Tanya!".

call_prover(metis, TPTP, TSTP) :- 
  atomic_list_concat(["timeout 60s metis --time-limit 60 --show proof ", TPTP, " > ", TSTP], CMD), 
  shell(CMD, _),
  open(TSTP, read, STRM), 
  read_line_to_string(STRM, _), 
  read_line_to_string(STRM, LINE), 
  close(STRM), 
  string_concat("% SZS status Unsatisfiable for", _, LINE).

mv_concat(FILE, LIST) :- 
  atomic_list_concat(LIST, PATH),
  mv(FILE, PATH).

bench(PROVER, CAT, ID) :- 
  atomics_to_string([CAT, ID, ".tptp"], TPTP),
  atomics_to_string([CAT, ID, ".tstp"], TSTP),
  atomics_to_string([CAT, ID, ".txtx"], TXTX),

  msg("Extracting problem from TPTP library"),
  call_tptp2x(CAT, ID), 

  msg('Begin ~w proof search', PROVER),
  (
    call_prover(PROVER, TPTP, TSTP) -> 
    (
      msg("Search successful, begin TSTP > TXTX compilation"),
      (
        call_compiler(PROVER, TPTP, TSTP, TXTX) -> 
        (
          msg("Compilation successful, verifying proof"),
          (
            verify(TPTP, TXTX) -> 
            ( 
              msg("Verification successful, saving files"),
              mv_concat(TPTP, [PROVER, "-tptp/ps.", TPTP]),
              mv_concat(TSTP, [PROVER, "-tstp/ps.", TSTP]),
              mv_concat(TXTX, [PROVER, "-txtx/ps.", TXTX])
            ) ; 
            ( 
              msg("Verification failed, saving files"),
              mv_concat(TPTP, [PROVER, "-tptp/vf.", TPTP]),
              mv_concat(TSTP, [PROVER, "-tstp/vf.", TSTP]),
              mv_concat(TXTX, [PROVER, "-txtx/vf.", TXTX])
            )
          )
        ) ;
        (
          msg("Compilation failed, saving files"),
          mv_concat(TPTP, [PROVER, "-tptp/cf.", TPTP]),
          mv_concat(TSTP, [PROVER, "-tstp/cf.", TSTP])
        )
      )
    ) ; 
    (
      msg("Search failed, deleting files"),
      delete_file(TPTP),
      delete_file(TSTP),
      false
    )
  ), !.

theorem_or_unsat(CAT, ID) :- 
  atomics_to_string(["/home/sk/programs/TPTP/Problems/", CAT, "/", CAT, ID, ".p"], FILE), 
  file_strings(FILE, STRS),
  member(STR, STRS), 
  split_string(STR, ":", " %", ["Status", STAT_STR]), 
  member(STAT_STR, ["Theorem", "Unsatisfiable"]).

choose_prob(PATHS, CAT, ID, REST) :- 
  random_pluck(PATHS, PATH, TEMP), 
  path_cat_id(PATH, RDM_CAT, RDM_ID), 
  (
    theorem_or_unsat(RDM_CAT, RDM_ID) ->
    (
      msg("Found theorem/unsat"),
      CAT = RDM_CAT, 
      ID = RDM_ID,
      REST = TEMP
    ) ; 
    (
      msg("Not theorem/unsat. Skipping..."),
      choose_prob(TEMP, CAT, ID, REST)
    )
  ).

bench_loop(_, 0, _).

bench_loop(PROVER, NUM, PATHS) :- 
  msg('Starting bench : ~w more problems to go', NUM),
  num_pred(NUM, PRED), 
  msg("Choosing random problem"), 
  % random_pluck(PATHS, PATH, REST), 
  % path_cat_id(PATH, CAT, ID), 
  choose_prob(PATHS, CAT, ID, REST),
  msg('Problem chosen = ~w~w', [CAT, ID]),
  (
    bench(PROVER, CAT, ID) ->
    bench_loop(PROVER, PRED, REST) ; 
    bench_loop(PROVER, NUM, PATHS)  
  ).

main([PROVER, NUM_ATOM]) :- 
  set_prolog_flag(stack_limit, 2_147_483_648),
  msg("Setting up bench session, generating paths"),
  rec_dir_files("/home/sk/programs/TPTP/Problems", ALL_PATHS), 
  include(is_fol_prob, ALL_PATHS, PATHS),
  atom_number(NUM_ATOM, NUM),
  msg("Enter bench loop"),
  bench_loop(PROVER, NUM, PATHS), 
  msg("Exit bench loop").