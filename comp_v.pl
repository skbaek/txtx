:- [compile].

fid_id(FID, ID) :- 
  atom_concat(f, IDAtom, FID),
  atom_number(IDAtom, ID).

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

v_intp_0(
  (ID, conjecture, TF, _),
  (ID, [], TF, cjtr)
).

v_intp_0(
 (ID, axiom, TPTP, _),
 (ID, [], TPTP, axm) 
).

v_intp_0(
  (ID, plain, (Prd <=> TPTP), introduced(avatar_definition,[new_symbols(naming,[Prd])])), 
  (ID, [], (Prd <=> TPTP), hyp(def(Prd))) 
) :- 
  Prd \= (~ _).

v_intp_0(
  (ID, plain, TPTP, introduced(predicate_definition_introduction,[new_symbols(naming, [Prd])])),
  (ID, [], NewTPTP, hyp(def(Prd))) 
) :- 
  pred_def_norm(TPTP, NewTPTP).

v_intp_0(
  (ID, _, TPTP, inference(Rul, _, IDs)),
  (ID, IDs, TPTP, Tac)
) :-
  rul_tac(Rul, Tac).

v_intp_0(
  (ID, _, TPTP, introduced(Rul, _)),
  (ID, [], TPTP, Tac) 
) :- 
  Rul \= predicate_definition_introduction,
  Rul \= avatar_definition,
  rul_tac(Rul, Tac).
  
v_intp_1((FID, FIDS, TF, TAC), (ID, IDs, SF, TAC)) :- 
  fid_id(FID, ID), 
  maplist_cut(fid_id, FIDS, IDs), 
  fof_form([], TF, FORM),
  (
    TAC = cjtr -> 
    SF = (- FORM) ;
    SF = (+ FORM)
  ).

v_intp(TUPLE, HINT) :- 
  v_intp_0(TUPLE, TEMP),
  v_intp_1(TEMP, HINT).

v_prec(Order, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  compare(Order, ID_A, ID_B).

v_tstp_hints(TSTP, HINTS) :- 
  trim_consult(TSTP),
  findall((ID, IDs, TF, Rul), fof(ID, IDs, TF, Rul), TUPLES),
  maplist_cut(v_intp, TUPLES, UNSORTED), 
  predsort(v_prec, UNSORTED, HINTS).

v_add((CID, [], (+ Conc), aoc), FIDs, Goal, [CID | TempFIDs], NewGoal) :- 
  get_aocs(Conc, Skms, AOCs),
  add_aocs(AOCs, Skms, FIDs, Goal, TempFIDs, TempGoal), 
  g_f(Conc, TempGoal, SubGoal, NewGoal), 
  goal_dfp(SubGoal, DFP), 
  aocs_opfs(AOCs, OPFs),
  aoc(OPFs, (0, (- Conc)), DFP).

v_add((CID, [], (+ Conc), hyp(Jst)), FIDs, Goal, [CID | FIDs], NewGoal) :- 
  g_h(+ Conc, Jst, Goal, NewGoal).

v_add((CID, [], (- Form), cjtr), FIDs, Goal, [CID | FIDs], NewGoal) :- 
  g_f(Form, Goal, NewGoal, TempGoal), 
  goal_dfp(TempGoal, DFP), 
  TempGoal = (CTX, _),
  get_prob(0, [CID | FIDs], CTX, PROB), 
  exclude(pos_osf, PROB, OSFS),
  pick_pmt_both(OSFS, (0, (+ Form)), DFP).

v_add((CID, [], (+ Form), axm), FIDs, Goal, [CID | FIDs], NewGoal) :- 
  g_f(Form, Goal, TempGoal, NewGoal), 
  goal_dfp(TempGoal, DFP), 
  TempGoal = (CTX, _),
  get_prob(0, [CID | FIDs], CTX, PROB), 
  exclude(neg_osf, PROB, OSFS),
  pick_pmt_both(OSFS, (0, (- Form)), DFP).

v_add((CID, PIDs, (+ Conc), Tac), FIDs, Goal, [CID | FIDs], NewGoal) :- 
  \+ member(Tac, [axm, cjtr, aoc, hyp(_)]),
  g_f(Conc, Goal, TempGoal, NewGoal), 
  goal_dfp(TempGoal, DFP), 
  maplist(fid_osf(TempGoal, [CID | FIDs]), PIDs, OSFs),
  call(Tac, OSFs, (0, (- Conc)), DFP), 
  DFP = (_, _, Prf), !, 
  ground_all(Prf),
  play_prf(Prf, TempGoal).

comp_v(TPTP, TSTP, TXTX) :-
  tptp_prob(TPTP, PROB),
  tstp_hints(v_intp, v_prec, TSTP, HINTS),
  elabs(v_add, HINTS, [], (PROB, 0, PRF)),
  ground(PRF),
  write_file_punct(TXTX, proof(PRF)).
