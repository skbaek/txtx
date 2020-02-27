#!/usr/bin/env swipl

:- initialization(main, main).

:- [comp_v, verify]. 


comp_v_args(['--compile', 'vampire', TPTP, TSTP, TXTX | _], TPTP, TSTP, TXTX).
comp_m_args(['--compile', 'metis', TPTP, TSTP, TXTX | _], TPTP, TSTP, TXTX).

verify_args(['--verify', TPTP, TXTX | _], TPTP, TXTX).

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