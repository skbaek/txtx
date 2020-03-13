:- [compile].

fid_id(FID, ID) :- 
  atom_concat('s', FID, ID).

rul_tac(negated_conjecture, ncjtr).  
rul_tac(cnf_transformation, v_cnf).
rul_tac(superposition, sup).  
rul_tac(forward_demodulation, fwd).
rul_tac(backward_demodulation, bwd).
rul_tac(definition_folding, dff).
rul_tac(definition_unfolding, dfu).
rul_tac(flattening, flt).  
rul_tac(skolemisation, skm).  
rul_tac(ennf_transformation, ennf).  
rul_tac(nnf_transformation, nnf).  
rul_tac(choice_axiom, aoc).
rul_tac(resolution, res).
rul_tac(subsumption_resolution, res).
rul_tac(avatar_sat_refutation, asr).
rul_tac(avatar_split_clause, spl).
rul_tac(avatar_contradiction_clause, ptblx).
rul_tac(avatar_component_clause, acmp).
rul_tac(factoring, wkn).
rul_tac(rectify, rtf).
rul_tac(equality_resolution, eqr).
rul_tac(equality_factoring, eqf).
rul_tac(duplicate_literal_removal, wkn).
rul_tac(trivial_inequality_removal, tir).
rul_tac(unused_predicate_definition_removal, updr).
rul_tac(true_and_false_elimination, tfe).
rul_tac(distinct_equality_removal, der).
rul_tac(pure_predicate_removal, ppr).
rul_tac(Rul, _) :- 
  format('Rule not found : ~w', Rul), 
  throw(no_tactic_for_rule). 

v_tuple_hint_0(
  (ID, conjecture, TF, _),
  (ID, [], TF, cjtr)
).

v_tuple_hint_0(
 (ID, axiom, TPTP, _),
 (ID, [], TPTP, axm) 
).

v_tuple_hint_0(
  (ID, plain, (PRD <=> TPTP), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  (ID, [], (PRD <=> TPTP), jst(["def", PRD_STR])) 
) :- 
  PRD \= (~ _),
  atom_string(PRD, PRD_STR).
  

v_tuple_hint_0(
  (ID, plain, TPTP, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  (ID, [], NewTPTP, jst(["def", PRD_STR])) 
) :- 
  pred_def_norm(TPTP, NewTPTP),
  atom_string(PRD, PRD_STR).

v_tuple_hint_0(
  (ID, _, TPTP, inference(Rul, _, IDs)),
  (ID, IDs, TPTP, Tac)
) :-
  rul_tac(Rul, Tac).

v_tuple_hint_0(
  (ID, _, TPTP, introduced(Rul, _)),
  (ID, [], TPTP, Tac) 
) :- 
  Rul \= predicate_definition_introduction,
  Rul \= avatar_definition,
  rul_tac(Rul, Tac).
  
v_tuple_hint_1((FID, FIDS, TF, cjtr), (ID, IDs, (- FORM), axm)) :- 
  fid_id(FID, ID), 
  maplist_cut(fid_id, FIDS, IDs), 
  fof_form([], TF, FORM).

v_tuple_hint_1((FID, FIDS, TF, TAC), (ID, IDs, (+ FORM), TAC)) :- 
  TAC \= cjtr,
  fid_id(FID, ID), 
  maplist_cut(fid_id, FIDS, IDs), 
  fof_form([], TF, FORM).

v_tuple_hint(TUPLE, HINT) :- 
  v_tuple_hint_0(TUPLE, TEMP),
  v_tuple_hint_1(TEMP, HINT).

v_cmp_hints(Order, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  atom_concat('sf', TEMP_A, ID_A),
  atom_number(TEMP_A, NUM_A),
  atom_concat('sf', TEMP_B, ID_B),
  atom_number(TEMP_B, NUM_B),
  compare(Order, NUM_A, NUM_B).

use_hint(STRM, (CID, [], SF, jst(JST)), FI, GOAL, FI, GOAL_N) :- 
  ts(some(STRM), CID, SF, JST, GOAL, GOAL_N).

use_hint(STRM, (CID, [], (+ CONC), aoc), FI, GOAL, FI_N, GOAL_N) :- 
  get_aocs(CONC, SKMS, AOCs),
  add_aocs(STRM, AOCs, SKMS, FI, GOAL, HYPS, FI_N, GOAL_T),
  ks(some(STRM), CID, CONC, GOAL_T, GOAL_S, GOAL_N), 
  snd(GOAL_S, FP), 
  aoc(HYPS, (CID, (- CONC)), (PRF, FP, FI_N)), 
  play_prf(STRM, PRF, GOAL_S).

use_hint(STRM, (CID, [], (- FORM), axm), FI, GOAL, FI_1, GOAL_N) :- 
  FI_1 is FI + 1, 
  FI_2 is FI + 2, 
  atom_concat(x, FI, CID0), 
  atom_concat(x, FI_1, CID1), 
  ks(some(STRM), CID0, (~ FORM), GOAL, GOAL_A, GOAL_B), 
  ns(some(STRM), CID0, CID1, GOAL_A, GOAL_C),
  GOAL_C = (CTX, FP),
  get_orig_hyps(CTX, HYPS),
  pick_pmt_both(HYPS, (CID1, (+ FORM)), (PRF, FP, FI_2)), 
  play_prf(STRM, PRF, GOAL_C), 
  ns(some(STRM), CID0, CID, GOAL_B, GOAL_N).

use_hint(STRM, (CID, [], (+ FORM), axm), FI, GOAL, FI, GOAL_N) :- 
  ks(some(STRM), CID, FORM, GOAL, GOAL_T, GOAL_N),
  GOAL_T = (CTX, FP),
  get_orig_hyps(CTX, HYPS),
  pick_pmt_both(HYPS, (CID, (- FORM)), (PRF, FP, FI)), 
  play_prf(STRM, PRF, GOAL_T).

use_hint(STRM, (CID, PIDS, (+ CONC), TAC), FI, GOAL, FI, GOAL_N) :- 
  \+ member(TAC, [axm, aoc, jst(_)]),
  ks(some(STRM), CID, CONC, GOAL, GOAL_T, GOAL_N), 
  GOAL_T = (CTX, FP), 
  maplist(prob_id_hyp(CTX), PIDS, HYPS),
  call(TAC, HYPS, (CID, (- CONC)), (PRF, FP, FI)), !, 
  ground_all(PRF),
  play_prf(STRM, PRF, GOAL_T).

use_hints(STRM, [HINT | HINTS], FI, GOAL) :-
  timed_call(
    500, 
    use_hint(STRM, HINT, FI, GOAL, FI_T, GOAL_T), 
    (
      report_elab_fail(HINT, FI, GOAL),
      throw(proof_compilation_failed)
    )
  ), !, 
  (
    HINTS = [] -> 
    HINT = (CID, _), 
    atom_concat(x, FI, NID),
    ts(some(STRM), NID, - $false, [neg_false], GOAL_T, GOAL_F),
    xs(some(STRM), CID, NID, GOAL_F) ; 
    use_hints(STRM, HINTS, FI_T, GOAL_T)
  ).

v_tstp_hints(TSTP, HINTS) :- 
  trim_consult(TSTP),
  findall((ID, IDs, TF, Rul), fof(ID, IDs, TF, Rul), TUPLES),
  maplist_cut(v_tuple_hint, TUPLES, UNSORTED), 
  predsort(v_cmp_hints, UNSORTED, HINTS).

comp_v(TPTP, TSTP, TXTX) :-
  tptp_prob(TPTP, PROB),
  v_tstp_hints(TSTP, HINTS),
  open(TXTX, write, STRM, [encoding(octet)]), 
  use_hints(STRM, HINTS, 0, (PROB, 0)),
  close(STRM).
  % write_file_punct(TXTX, proof(PRF)).


