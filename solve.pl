:- [basic].

id_sid(ID, SID) :- 
  atom_concat('s', ID, SID).

%rul_hint(cnf_transformation, v_cnf).
% rul_hint(flattening, flt).  
% rul_hint(skolemisation, skm).  
% rul_hint(ennf_transformation, ennf).  
% rul_hint(nnf_transformation, nnf).  
% rul_hint(avatar_component_clause, acmp).
% rul_hint(rectify, rtf).
% rul_hint(factoring, wkn).
% rul_hint(duplicate_literal_removal, wkn).
% rul_hint(true_and_false_elimination, tfe).
% rul_hint(pure_predicate_removal, ppr).
% rul_hint(distinct_equality_removal, der).

rul_hint(superposition, (sup, l)).  
rul_hint(forward_demodulation, (sup, l)).
rul_hint(backward_demodulation, (sup, r)).
rul_hint(resolution, res).
rul_hint(subsumption_resolution, res).
rul_hint(trivial_inequality_removal, eqr).
rul_hint(equality_resolution, eqr).
rul_hint(equality_factoring, eqf).

rul_hint(cnf_transformation, dtrx).
rul_hint(factoring, dtrx).
rul_hint(avatar_component_clause, dtrx).
rul_hint(avatar_contradiction_clause, pblx).
rul_hint(duplicate_literal_removal, dtrx).

% axiom
% conjecture
rul_hint(negated_conjecture, parac).  
rul_hint(flattening, parac).  
rul_hint(ennf_transformation, paras).  
rul_hint(rectify, paral).
rul_hint(true_and_false_elimination, paratf).
rul_hint(pure_predicate_removal, parad).
rul_hint(nnf_transformation, vnnf).  

rul_hint(avatar_sat_refutation, sat).
rul_hint(unused_predicate_definition_removal, updr).
rul_hint(avatar_split_clause, spl).
rul_hint(definition_folding, dff).
rul_hint(definition_unfolding, dfu).
rul_hint(choice_axiom, gaoc).
rul_hint(skolemisation, skm).  
% avatar_definition
% predicate_definition_introduction

rul_hint(RUL, _) :- 
  format('Rule not found : ~w', RUL), 
  throw(no_tactic_for_rule). 

rul_hints(RUL, [HINT]) :-
  rul_hint(RUL, HINT).

pred_def_norm(! Xs : TPTP, ! Xs : NewTPTP) :- 
  pred_def_norm(TPTP, NewTPTP).

pred_def_norm((TPTP | ~ Atom), (Atom <=> TPTP)).
pred_def_norm((Atom <=> TPTP), (Atom <=> TPTP)).

v_tup_inst(
  PIDS,
  (ID, conjecture, TF, _),
  inf([parac, dtrx], PIDS, SID, (- FORM))
) :- 
  id_sid(ID, SID), 
  fof_form([], TF, FORM).
  
v_tup_inst(
 PIDS,
 (ID, axiom, TF, _),
 inf([parac, dtrx], PIDS, SID, (+ FORM)) 
) :-
  id_sid(ID, SID), 
  fof_form([], TF, FORM).

v_tup_inst(
  _,
  (ID, plain, (PRD <=> TF), introduced(avatar_definition,[new_symbols(naming,[PRD])])), 
  add([def, PRD], SID, (+ FORM))
) :- 
  PRD \= (~ _),
  id_sid(ID, SID), 
  fof_form([], (PRD <=> TF), FORM).
  
v_tup_inst(
  _,
  (ID, plain, TF, introduced(predicate_definition_introduction,[new_symbols(naming, [PRD])])),
  add([def, PRD], SID, (+ FORM))
) :- 
  pred_def_norm(TF, TEMP),
  id_sid(ID, SID), 
  fof_form([], TEMP, FORM).

v_tup_inst(
  _, 
  (ID, _, TF, introduced(RUL, _)),
  add(HINTS, SID, (+ FORM))
) :- 
  RUL \= predicate_definition_introduction,
  RUL \= avatar_definition,
  rul_hints(RUL, HINTS),
  id_sid(ID, SID), 
  fof_form([], TF, FORM).
  
v_tup_inst(
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

update_seen(SEEN, [], SEEN, []).

update_seen(SEEN_I, [ID | IDS], SEEN_O, DELS) :- 
  get_assoc(ID, SEEN_I, c) -> 
  update_seen(SEEN_I, IDS, SEEN_O, DELS) 
;
  put_assoc(ID, SEEN_I, c, SEEN_T),
  DELS = [del(ID) | DELS_T], 
  update_seen(SEEN_T, IDS, SEEN_O, DELS_T). 

insert_dels([], EMP, []) :- 
  empty_assoc(EMP).
  
insert_dels([INST | INSTS_I], SEEN, INSTS_O) :- 
  insert_dels(INSTS_I, SEEN_T, INSTS_T), 
  (
    INST = del(_) -> 
    throw(invalid_deletion)
  ; 
    INST = add(_, _, _) -> 
    SEEN = SEEN_T,
    INSTS_O = [INST | INSTS_T]
  ;
    INST = inf(_, IDS, _, _), 
    sort(IDS, IDS_S), 
    update_seen(SEEN_T, IDS_S, SEEN, DELS), 
    append([INST | DELS], INSTS_T, INSTS_O)
  ).

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
  paral(((0, (+ ANTE)), (1, (- CONS)), (_, FP, 2))).

id_skm_aoc_inst(ID, SKM, AOC, add([aoc, SKM], ID, (+ AOC))).

mk_del(ID, del(ID)).

reduce_gaocs([], []).

reduce_gaocs([INST | INSTS], SOL) :- 
  (
    INST = add([gaoc], ID, (+ FORM)) -> 
    get_aocs(FORM, SKMS, AOCS),
    length(SKMS, LTH),
    range(0, LTH, NUMS),
    maplist_cut(atom_concat(t), NUMS, IDS),
    maplist_cut(id_skm_aoc_inst, IDS, SKMS, AOCS, ADDS), 
    append(ADDS, [inf([gaoc], IDS, ID, (+ FORM))], PFX) ;
    PFX = [INST]
  ),
  reduce_gaocs(INSTS, SFX),
  append(PFX, SFX, SOL). 


id_tup(ID, (fof, ID, ROLE, TF, none, none)) :- fof(ID, ROLE, TF).
id_tup(ID, (fof, ID, ROLE, TF, SRC, none)) :- fof(ID, ROLE, TF, SRC).
id_tup(ID, (fof, ID, ROLE, TF, SRC, ANT)) :- fof(ID, ROLE, TF, SRC, ANT).
id_tup(ID, (cnf, ID, ROLE, TF, none, none)) :- cnf(ID, ROLE, TF).
id_tup(ID, (cnf, ID, ROLE, TF, SRC, none)) :- cnf(ID, ROLE, TF, SRC).
id_tup(ID, (cnf, ID, ROLE, TF, SRC, ANT)) :- cnf(ID, ROLE, TF, SRC, ANT).

e_rul_pred(assume_negation, an).
e_rul_pred(split_conjunct, sc).
e_rul_pred(fof_nnf, fn).
e_rul_pred(RUL, RUL) :- 
  member(RUL, [rw, ef, sr, pm, er, cn]).

axiomatic(TYPE) :- 
  member(TYPE, [axiom, hypothesis, conjecture, negated_conjecture]).

e_ant_id(ID, ID) :- atom(ID).
e_ant_id(inference(_, _, [ANT]), ID) :- e_ant_id(ANT, ID).

e_ant_ids_nst(ID, [ID], id(ID)) :- atom(ID).

e_ant_ids_nst(
  inference(RUL, _, [ANT]),
  IDS, 
  unst(PRED, NST)
) :-  
  e_rul_pred(RUL, PRED),
  e_ant_ids_nst(ANT, IDS, NST).

e_ant_ids_nst(
  inference(RUL, _, [ANT_A, ANT_B]),
  IDS, 
  bnst(PRED, NST_A, NST_B)
) :-  
  e_rul_pred(RUL, PRED),
  e_ant_ids_nst(ANT_A, IDS_A, NST_A), 
  e_ant_ids_nst(ANT_B, IDS_B, NST_B), 
  union(IDS_A, IDS_B, IDS).

e_tup_inst(
  (_, _, TYPE, _, file(_, _), none),
  none
) :- 
  axiomatic(TYPE).

e_tup_inst(
  (LNG, CID, TYPE, TF, PID, none),
  some(inf([parac, dtrx], [PID], CID, (+ FORM)))
) :- 
  axiomatic(TYPE),
  atom(PID), !, 
  tf_form(LNG, TF, FORM).
  
e_tup_inst(
  (LNG, ID, _, TF, ANT, _),
  some(inf([nst(NST)], IDS, ID, (+ FORM)))
) :- 
  tf_form(LNG, TF, FORM), 
  e_ant_ids_nst(ANT, IDS, NST).

e_tup_inst(
  (LNG, CID, _, TF, ANT, _),
  some(inf([dtrx], [PID], CID, (+ FORM)))
) :- 
  tf_form(LNG, TF, FORM), 
  e_ant_id(ANT, PID).


%%%%%%%%%%%%%%%% METIS %%%%%%%%%%%%%%%%

metis_tuple_inst(
  PIDS, 
  (LNG, ID, conjecture, TF, _),
  inf([parac], PIDS, SID, (- FORM))
) :- !,
  atom_concat(s, ID, SID),
  tf_form(LNG, TF, FORM).

metis_tuple_inst(
 PIDS,
 (LNG, ID, TYPE, TF, _),
 inf([parac], PIDS, SID, (+ FORM)) 
) :- 
  member(TYPE, [axiom, hypothesis, negated_conjecture]), !,
  atom_concat(s, ID, SID),
  tf_form(LNG, TF, FORM).

metis_tuple_inst(
  _,
  (LNG, ID, plain, TF, ANT),
  inf(HINTS, SIDS, SID, (+ FORM)) 
) :- 

  atom_concat(s, ID, SID),
  tf_form(LNG, TF, FORM),
  ant_ids_hints(ANT, IDS, HINTS), 
  maplist_cut(atomic_concat(s), IDS, SIDS). 

ant_ids_hints(inference(subst, [], [PID : _]), [PID], [subst]).

ant_ids_hints(inference(RUL, _, IDS), IDS, [HINT]) :- 
  RUL \= subst, 
  metis_rul_hint(RUL, HINT).

ant_ids_hints(introduced(tautology, [refl, _]), [], refl).

ant_ids_hints(introduced(tautology, [equality, _]), [], eq).

ant_ids_hints(introduced(RUL), [], [HINT]) :- 
  RUL \= tautology,
  metis_rul_hint(RUL, HINT).

metis_rul_hint(strip, strip).
metis_rul_hint(canonicalize, canon).
metis_rul_hint(specialize, spec).
metis_rul_hint(negate, neg).
metis_rul_hint(simplify, simp).
metis_rul_hint(resolve, res).
metis_rul_hint(clausify, cla).
metis_rul_hint(conjunct, conj).

string_id(STR, ID) :- 
  split_string(STR, ",(", " ", [LNG, ID_STR | _]), 
  member(LNG, ["cnf", "fof"]),
  atom_string(ID, ID_STR).

sorted_ids(TSTP, IDS) :-
  file_strings(TSTP, STRS),
  maplist_try(string_id, STRS, IDS).

solve('e', _, TSTP, SOL) :- 
  trim_consult(TSTP),
  sorted_ids(TSTP, IDS), 
  maplist_cut(id_tup, IDS, TUPS), 
  maplist_opt(e_tup_inst, TUPS, SOL),
  true.

solve('metis', PIDS, TSTP, SOL) :- 
  trim_consult(TSTP),
  sorted_ids(TSTP, IDS), 
  maplist_cut(id_tup, IDS, TUPS), 
  maplist_cut(metis_tuple_inst(PIDS), TUPS, SOL),
  true.

solve('vampire', PIDS, TSTP, SOL) :- 
  trim_consult(TSTP),
  findall((ID, IDS, TF, RUL), fof(ID, IDS, TF, RUL), UNSORTED),
  predsort(vampire_cmp_hints, UNSORTED, SORTED), 
  maplist_cut(v_tup_inst(PIDS), SORTED, INSTS), 
  write("Computing deletions...\n"),
  insert_dels(INSTS, _, DELETED),
  write("Deletions found.\n"),
  reduce_gaocs(DELETED, SOL),
  write("Solution found.\n").