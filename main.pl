#!/usr/bin/env swipl

:- initialization(main, main).

:- [prove, vsol]. 

tstp_sol('vampire', PIDS, TSTP, SOL) :- 
  vampire_tstp_sol(PIDS, TSTP, SOL).

test_all([]).
test_all([TPTP | TPTPS]) :- 
  format("Solving problem : ~w\n\n", TPTP),
  atomic_concat("vp/", TPTP, PATH),
  main(['-t', PATH]), 
  format("Verifying proof : ~w\n\n", TPTP),
  main(['-v', PATH, "temp.txtx"]), 
  test_all(TPTPS).

main(['-tl']) :- 
  file_strings("/home/sk/problist", TPTPS), 
  time(test_all(TPTPS)).

main(['-t', TPTP]) :- 
  style_check(-singleton),
  atom_string(TPTP, STR),
  string_concat("vp/", TEMP, STR), 
  string_concat(NAME, ".tptp", TEMP), 
  atomics_to_string(["vs/", NAME, ".tstp"], TSTP),
  tptp_prob(TPTP, PIDS, PROB),
  tstp_sol(PRVR, PIDS, TSTP, SOL),
  open("temp.txtx", write, STRM, [encoding(octet)]),
  prove(STRM, PRVR, SOL, PROB),
  close(STRM).

main(['-p', PRVR, TPTP, TSTP, TXTX]) :- 
  style_check(-singleton),
  tptp_prob(TPTP, PIDS, PROB),
  tstp_sol(PRVR, PIDS, TSTP, SOL),
  open(TXTX, write, STRM, [encoding(octet)]),
  prove(STRM, PRVR, SOL, PROB),
  close(STRM).
  
main(['-v', TPTP, TXTX]) :- 
  style_check(-singleton),
  tptp_prob(TPTP, _, PROB),
  open(TXTX, read, STRM, [encoding(octet)]), 
  % verify(STRM, PROB, 0), 
  get_prf(STRM, PRF),
  verify(PROB, 0, PRF),
  write("Proof verified.\n"),
  close(STRM).


% TODO :  
% - Deletion instructions 
% - Omit mid-elaboration verification
% - Implicit function application 
% - Directional matrix
% - Streaming verification

% comp_m_args(['--compile', 'metis', TPTP, TSTP, TXTX | _], TPTP, TSTP, TXTX).
% 
% verify_args(['--verify', TPTP, TXTX | _], TPTP, TXTX).

/*
help_msg :-
  write(
"=========== Usage ==========\n
Call TX2P using\n 
  TX2P --compile [prover] [TPTP file] [TSTP file] [output path]\n
to compile a TSTP proof into TXTX format and save the result at [output path]\n
  TX2P --verify [TPTP file] [TXTX file]\n
to verify that [TXTX file] is a valid proof of [TPTP file]\n
=========== End ==========\n"
  ).

main(ARGV) :-
  style_check(-singleton),
  (
    ( ARGV = ['-h'], 
      help_msg ) ;
    ( comp_v_args(ARGV, TPTP, TSTP, TXTX), 
      comp_v(TPTP, TSTP, TXTX) ) ;
    % ( comp_m_args(ARGV, TPTP, TSTP, TXTX), 
    %    comp_m(TPTP, TSTP, TXTX) ) ;
    ( verify_args(ARGV, TPTP, TXTX), 
      verify(TPTP, TXTX) ) 
  ).
*/