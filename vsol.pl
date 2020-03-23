:- [basic].

id_sid(ID, SID) :- 
  atom_concat('s', ID, SID).

rul_hint(negated_conjecture, parac).  
%rul_hint(cnf_transformation, v_cnf).
rul_hint(cnf_transformation, ptrx).
rul_hint(superposition, (sup, l)).  
rul_hint(forward_demodulation, (sup, l)).
rul_hint(backward_demodulation, (sup, r)).
rul_hint(definition_folding, dff).
rul_hint(definition_unfolding, dfu).
% rul_hint(flattening, flt).  
rul_hint(flattening, ptrx).  
% rul_hint(skolemisation, skm).  
rul_hint(skolemisation, mtrx).  
% rul_hint(ennf_transformation, ennf).  
rul_hint(ennf_transformation, ptrx).  
% rul_hint(nnf_transformation, nnf).  
rul_hint(nnf_transformation, ptrx).  
rul_hint(resolution, res).
rul_hint(subsumption_resolution, res).

% rul_hint(avatar_sat_refutation, asr).
rul_hint(avatar_sat_refutation, sat).

% rul_hint(avatar_split_clause, spl).
rul_hint(avatar_split_clause, mtrx).

% rul_hint(avatar_contradiction_clause, ptblx).
rul_hint(avatar_contradiction_clause, pblx).

rul_hint(avatar_component_clause, ptrx).
% rul_hint(avatar_component_clause, acmp).
% rul_hint(factoring, wkn).
rul_hint(factoring, ptrx).
% rul_hint(rectify, rtf).
rul_hint(rectify, ptrx).
rul_hint(equality_resolution, eqr).
rul_hint(equality_factoring, eqf).
% rul_hint(duplicate_literal_removal, wkn).
rul_hint(duplicate_literal_removal, ptrx).
rul_hint(trivial_inequality_removal, eqr).
rul_hint(unused_predicate_definition_removal, ptrx).
rul_hint(true_and_false_elimination, tfe).
rul_hint(distinct_equality_removal, der).
% rul_hint(pure_predicate_removal, ppr).
rul_hint(pure_predicate_removal, parac).
rul_hint(choice_axiom, gaoc).
rul_hint(RUL, _) :- 
  format('RULe not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

rul_hints(RUL, [HINT]) :-
  rul_hint(RUL, HINT).

pred_def_norm(! Xs : TPTP, ! Xs : NewTPTP) :- 
  pred_def_norm(TPTP, NewTPTP).

pred_def_norm((TPTP | ~ Atom), (Atom <=> TPTP)).
pred_def_norm((Atom <=> TPTP), (Atom <=> TPTP)).

vampire_tuple_inst(
  PIDS,
  (ID, conjecture, TF, _),
  inf([parac, ptrx], PIDS, SID, (- FORM))
) :- 
  id_sid(ID, SID), 
  fof_form([], TF, FORM).
  
vampire_tuple_inst(
 PIDS,
 (ID, axiom, TF, _),
 inf([parac, ptrx], PIDS, SID, (+ FORM)) 
) :-
  id_sid(ID, SID), 
  fof_form([], TF, FORM).

vampire_tuple_inst(
  _,
  (ID, plain, (PRD <=> TF), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  add([def, PRD], SID, (+ FORM))
) :- 
  PRD \= (~ _),
  id_sid(ID, SID), 
  fof_form([], (PRD <=> TF), FORM).
  
vampire_tuple_inst(
  _,
  (ID, plain, TF, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  add([def, PRD], SID, (+ FORM))
) :- 
  pred_def_norm(TF, TEMP),
  id_sid(ID, SID), 
  fof_form([], TEMP, FORM).

vampire_tuple_inst(
  _, 
  (ID, _, TF, introduced(RUL, _)),
  add(HINTS, SID, (+ FORM))
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hints(RUL, HINTS),
  id_sid(ID, SID), 
  fof_form([], TF, FORM).
  
vampire_tuple_inst(
  _, 
  (ID, _, TF, inference(RUL, _, IDS)),
  inf(HINTS, SIDS, SID, (+ FORM))
) :-
  rul_hints(RUL, HINTS),
  id_sid(ID, SID), 
  maplist_cut(id_sid, IDS, SIDS),
  fof_form([], TF, FORM).

vampire_cmp_hints(ORD, (ID_A, _, _, _), (ID_B, _, _, _)) :- 
  atom_concat('f', TEMP_A, ID_A),
  atom_number(TEMP_A, NUM_A),
  atom_concat('f', TEMP_B, ID_B),
  atom_number(TEMP_B, NUM_B),
  compare(ORD, NUM_A, NUM_B).

insert_dels(X, X).

thread([], X, X).
thread([GOAL | GOALS], X, Z) :-
  call(GOAL, X, Y), 
  thread(GOALS, Y, Z).

revert_pars_par(NUM, IDX, #(DIFF)) :- 
  DIFF is NUM - IDX.

revert_pars_term(NUM, TERM_I, TERM_O) :- 
  map_par(revert_pars_par(NUM), TERM_I, TERM_O).

revert_pars(CNT, FORM, AOC) :- 
  NUM is CNT - 1,
  map_form(revert_pars_term, NUM, FORM, TEMP), 
  add_fas(CNT, TEMP, AOC).

get_fun(TERM, FUN) :-
  TERM =.. [FUN | _].

get_aocs(FORM, SKMS, AOCS) :- 
  inst_with_pars(0, FORM, CNT, ANTE => CONS), 
  mk_pars(CNT, PARS),
  get_aocs_aux(PARS, CNT, ANTE, CONS, SKM_TERMS, FORMS),
  maplist_cut(get_fun, SKM_TERMS, SKMS),
  maplist_cut(revert_pars(CNT), FORMS, AOCS).

get_aocs_aux(ARGS, FP, ? ANTE, CONS, [TERM | TERMS], [(? ANTE) => ANTE_O | AOCS]) :- !,
  subst_form(TERM, ANTE, ANTE_O), 
  get_aocs_aux(ARGS, FP, ANTE_O, CONS, TERMS, AOCS).

get_aocs_aux(_, FP, ANTE, CONS, [], []) :- 
  para_aoc(((0, (+ ANTE)), (1, (- CONS)), (_, FP, 2))).

para_aoc(TRP) :- 
  para_zero(TRP) -> true ; 
  para_one_lax(TRP, TRP_N) -> para_aoc(TRP_N) ; 
  para_two(TRP, TRP_L, TRP_R), 
  para_aoc(TRP_L),
  para_aoc(TRP_R).

id_skm_aoc_inst(ID, SKM, AOC, add([aoc, SKM], ID, (+ AOC))).

mk_del(ID, del(ID)).

reduce_gaocs([], []).

reduce_gaocs([INST | INSTS], SOL) :- 
  (
    INST = add([gaoc], ID, (+ FORM)) -> 
    write("GCA detected\n"),
    get_aocs(FORM, SKMS, AOCS),
    length(SKMS, LTH),
    range(0, LTH, NUMS),
    maplist_cut(atom_concat(t), NUMS, IDS),
    maplist_cut(id_skm_aoc_inst, IDS, SKMS, AOCS, ADDS), 
    maplist_cut(mk_del, IDS, DELS),
    append(ADDS, [inf([gaoc], IDS, ID, (+ FORM)) | DELS], PFX) ;
    PFX = [INST]
  ),
  reduce_gaocs(INSTS, SFX),
  append(PFX, SFX, SOL). 

vampire_tstp_sol(PIDS, TSTP, SOL) :- 
  trim_consult(TSTP),
  findall((ID, IDS, TF, RUL), fof(ID, IDS, TF, RUL), UNSORTED),
  predsort(vampire_cmp_hints, UNSORTED, SORTED), 
  maplist_cut(vampire_tuple_inst(PIDS), SORTED, INSTS), 
  insert_dels(INSTS, DELETED),
  reduce_gaocs(DELETED, SOL).