#!/usr/bin/env swipl

:- initialization(main, main).

:- [prove, vsol, verify]. 

tstp_sol('vampire', PIDS, TSTP, SOL) :- 
  vampire_tstp_sol(PIDS, TSTP, SOL).

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
  verify(STRM, PROB, 0), 
  write("Proof verified.\n"),
  close(STRM).

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