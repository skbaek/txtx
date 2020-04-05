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

mk(SYM, ARG, TERM) :- 
  TERM =.. [SYM, ARG].

mk_dels(NUM, DELS) :- 
  range(0, NUM, NUMS),
  maplist_cut(mk(t), NUMS, IDS),
  maplist_cut(mk(del), IDS, DELS).

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

axiomatic(TYPE) :- 
  member(TYPE, [axiom, hypothesis, conjecture, negated_conjecture]).

mk_rw(ATOM, ~ FORM, ~ RW) :- !,
  mk_rw(ATOM, FORM, RW).

mk_rw(ATOM, (FORM_L | FORM_R), (RW_L | RW_R)) :- !,
  mk_rw(ATOM, FORM_L, RW_L), 
  mk_rw(ATOM, FORM_R, RW_R).

mk_rw(ATOM, FORM, RW) :- 
  ATOM == FORM -> RW = $true ; 
  RW = FORM.

mk_rw_form(LHS, RHS, ~ FORM, ~ RW) :- !,
  mk_rw_form(LHS, RHS, FORM, RW).

mk_rw_form(LHS, RHS, (FORM_L | FORM_R), (RW_L | RW_R)) :- !,
  (
    mk_rw_form(LHS, RHS, FORM_L, RW_L),
    FORM_R = RW_R
  ;
    mk_rw_form(LHS, RHS, FORM_R, RW_R),
    FORM_L = RW_L
  ).

mk_rw_form(LHS, RHS, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I], 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O), 
  FORM_O =.. [REL | TERMS_O]. 

mk_rw_terms(LHS, RHS, [TERM_I | TERMS_I], [TERM_O | TERMS_O]) :-  
  mk_rw_term(LHS, RHS, TERM_I, TERM_O),
  TERMS_I = TERMS_O 
;
  TERM_I = TERM_O, 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O).

mk_rw_term(LHS, RHS, TERM_I, TERM_O) :- 
  unify_with_occurs_check(LHS, TERM_I),
  unify_with_occurs_check(RHS, TERM_O)
; 
  \+ var(TERM_I),
  TERM_I =.. [FUN | TERMS_I], 
  mk_rw_terms(LHS, RHS, TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

mk_cf([], $false).
mk_cf([LIT], LIT) :- !.
mk_cf([LIT | LITS], LIT | CLA) :-
  mk_cf(LITS, CLA).

nst_orient(pm, HYP_L, HYP_R, HYP_L, HYP_R).
nst_orient(sr, HYP_L, HYP_R, HYP_R, HYP_L).

pull_ovs(_, [], FORM, FORM).
pull_ovs(CNT, [NUM | NUMS], FORM, NORM) :- 
  safe_subst_form(NUM, #(CNT), FORM, TEMP), 
  SUCC is CNT + 1,
  pull_ovs(SUCC, NUMS, TEMP, NORM).

pull_ovs(FORM, NORM) :- 
  ovs(FORM, OVS), 
  pull_ovs(0, OVS, FORM, NORM).

skolemize(SYMBS, FORM, SKM, AOC, NORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !, 
  (
    skolemize(SYMBS, FORM_A, SKM, AOC, NORM_A), 
    NORM_B = FORM_B
  ;
    skolemize(SYMBS, FORM_B, SKM, AOC, NORM_B), 
    NORM_A = FORM_A
  ), 
  NORM =.. [BCT, NORM_A, NORM_B].

skolemize(SYMBS, ~ FORM, SKM, AOC, ~ NORM) :- !,
  skolemize(SYMBS, FORM, SKM, AOC, NORM).

skolemize(SYMBS, ! FORM, SKM, AOC, ! NORM) :- !,
  skolemize(SYMBS, FORM, SKM, AOC, NORM).

skolemize(FAS, ? FORM, SKM, AOC, NORM) :-  
  ovs(FORM, NUMS), 
  sort(NUMS, [0 | SORTED]), 
  length(SORTED, LTH),
  maplist(num_pred, SORTED, PREDS),
  reverse(PREDS, REV), 
  maplist_cut(mk('#'), REV, VARS), 
  member((SKM, LTH), FAS), 
  SKM_TERM =.. [SKM | VARS], 
  safe_subst_form(SKM_TERM, FORM, NORM),
  % pull_ovs(0, SORTED, FORM, ANTE),
  % pull_ovs(0, SORTED, NORM, CONS),
  pull_ovs((? FORM) => NORM, TEMP),
  ov_bound(TEMP, NUM),
  add_fas(NUM, TEMP, AOC).


last_id([inf(_,  _, ID, _) | _], ID).

pairs_insts(FI, [], FI, [], []).
pairs_insts(FI_I, [(SKM, AOC) | PAIRS], FI_O, [t(FI_I) | IDS], [add([aoc, SKM], t(FI_I), (+ AOC)) | INSTS]) :- 
  FI_T is FI_I + 1, 
  pairs_insts(FI_T, PAIRS, FI_O, IDS, INSTS).
  
unroll_hint(
  skm(PAIRS), FI_I, PID, SF, FI_O, t(FI_T), 
  [inf([skm], [PID | IDS], t(FI_T), SF) | INSTS]
) :- !, 
  pairs_insts(FI_I, PAIRS, FI_T, IDS, REV_INSTS),
  FI_O is FI_T + 1,
  reverse(REV_INSTS, INSTS).

unroll_hint(
  HINT, FI_I, PID, SF, FI_O, t(FI_I), 
  [inf([HINT], [PID], t(FI_I), SF)]
) :- 
  FI_O is FI_I + 1.

unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX) :- 
  format("Cannot unroll hint : ~w\n\n", unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX)).

unroll_hint(HINT, FI_I, SID, MID, SF, FI_O, t(FI_I), 
  [inf([HINT], [SID, MID], t(FI_I), SF)]
) :- 
  FI_O is FI_I + 1.

unroll_tree(FI, ntr(ID, _), FI, ID, []).

unroll_tree(
  FI_I, 
  utr(TREE, HINT, SF), 
  FI_O, 
  CID,
  INSTS   
) :- 
  unroll_tree(FI_I, TREE, FI_T, PID, SFX), 
  unroll_hint(HINT, FI_T, PID, SF, FI_O, CID, PFX),
  append(PFX, SFX, INSTS).

unroll_tree(
  FI_I, 
  btr(TREE_A, TREE_B, HINT, SF), 
  FI_O, 
  CID,
  INSTS   
) :- 
  unroll_tree(FI_I, TREE_A, FI_1, SID, SFX), 
  unroll_tree(FI_1, TREE_B, FI_2, MID, MFX), 
  unroll_hint(HINT, FI_2, SID, MID, SF, FI_O, CID, PFX),
  append([PFX, MFX, SFX], INSTS).

perm_cla(CLA_I, CLA_O) :- 
  cf_lits(CLA_I, LITS),
  permutation(LITS, PERM), 
  mk_cf(PERM, CLA_O).

eq_resolve(FORM_I, FORM_O) :- 
  inst_fas(FORM_I, BODY_I), 
  cf_lits(BODY_I, LITS),
  pluck(LITS, ~ (LHS = RHS), REST), 
  unify_with_occurs_check(LHS, RHS), 
  mk_cf(REST, BODY_O),
  close_lvs(BODY_O, FORM_O).
  
conjunct(FORM, CONJ) :- 
  inst_fas(FORM, BODY), 
  conjunct_core(BODY, TEMP), 
  perm_cla(TEMP, PERM), 
  close_lvs(PERM, CONJ).

conjunct_core(FORM_A & FORM_B, NORM) :- !, 
  (
    conjunct_core(FORM_A, NORM) ;
    conjunct_core(FORM_B, NORM)
  ).
conjunct_core(FORM, FORM).

tree_conc(ntr(_, SF), SF).
tree_conc(utr(_, _, SF), SF).
tree_conc(btr(_, _, _, SF), SF).

mk_root(_, assume_negation, - FORM, ngt, + ~ FORM).
mk_root(_, shift_quantors, + FORM, upnf, + NORM) :- upnf(FORM, NORM).
mk_root(_, fof_nnf, + FORM, fnnf, + NORM) :- fnnf([], FORM, NORM).
mk_root(_, variable_rename, + FORM, rnm, + FORM).
mk_root(_, fof_simplification, + FORM, rnm, + FORM).
mk_root(_, split_conjunct, + FORM, scj, + NORM) :- conjunct(FORM, NORM).
mk_root(_, cn, + FORM, paratf, + NORM) :- bool_norm(FORM, NORM).
mk_root(_, distribute, + FORM, dist, + NORM) :- distribute(FORM, NORM).
mk_root(_, er, + FORM, eqr, + NORM) :- eq_resolve(FORM, NORM).
mk_root(_, ef, + FORM_I, pmt, + FORM_O) :- 
  inst_fas(FORM_I, BODY_I),
  cf_lits(BODY_I, LITS), 
  pluck(2, LITS, [LIT_A, LIT_B], REST),
  unify_with_occurs_check(LIT_A, LIT_B), 
  mk_cf([LIT_A | REST], BODY_O), 
  close_lvs(BODY_O, FORM_O).

% mk_root(FAS, skolemize, + FORM, skm(SKM, AOC), + NORM) :- skolemize(FAS, FORM, SKM, AOC, NORM).
mk_root(FAS, skolemize, + FORM, skm(PAIRS), + NORM) :- 
  skolemize_many(FAS, FORM, PAIRS, NORM).

skolemize_many(_, FORM, [], FORM) :- \+ has_exists(FORM).
skolemize_many(FAS, FORM, [(SKM, AOC) | HINTS], NORM) :- 
  skolemize(FAS, FORM, SKM, AOC, TEMP), 
  skolemize_many(FAS, TEMP, HINTS, NORM).

mk_root(_, pm, + FORM_A, + FORM_B, (sup, l), + FORM) :- 
  inst_fas(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A), 
  pluck(LITS_A, LIT_A, REST_A),
  inst_fas(FORM_B, BODY_B),
  % cf_lits(BODY_B, [LIT_B | LITS_B]), 
  cf_lits(BODY_B, LITS_B), 
  pluck(LITS_B, LIT_B, REST_B),
  erient_form(LIT_B, LHS = RHS), 
  mk_rw_form(LHS, RHS, LIT_A, LIT_N), 
  append([LIT_N | REST_A], REST_B, LITS),
  mk_cf(LITS, BODY_N),
  close_lvs(BODY_N, FORM).

mk_root(_, rw, + FORM_A, + FORM_B, dfu, + FORM) :- 
  inst_fas(FORM_A, BODY_A),
  inst_fas(FORM_B, BODY_B),
  BODY_B = (LHS = RHS), %erient_form(BODY_B, LHS = RHS), 
  mk_rw_form(LHS, RHS, BODY_A, BODY_N), 
  close_lvs(BODY_N, FORM).

mk_root(_, RUL, + FORM_A, + FORM_B, res, + FORM) :- 
  member(RUL, [sr, pm]), 
  inst_fas(FORM_A, BODY_A),
  inst_fas(FORM_B, BODY_B),
  nst_orient(RUL, BODY_A, BODY_B, BODY_L, BODY_R),
  cf_lits(BODY_L, LITS_L), 
  cf_lits(BODY_R, LITS_R), 
  pluck(LITS_L, ~ ATOM_L, REST_L),
  pluck(LITS_R, ATOM_R, REST_R),
  unify_atom(ATOM_L, ATOM_R),
  exclude('=='(~ ATOM_L), REST_L, FILT_L), 
  exclude('=='(ATOM_R), REST_R, FILT_R), 
  append(FILT_L, FILT_R, LITS),
  mk_cf(LITS, CF),
  close_lvs(CF, FORM).
  
mk_root(_, rw, + FORM_A, + FORM_B, rwa, + FORM) :- 
  inst_fas(FORM_A, BODY_A),
  inst_fas(FORM_B, BODY_B),
  cf_atoms(BODY_A, ATOMS), 
  member(ATOM, ATOMS), 
  unify_with_occurs_check(ATOM, BODY_B),
  mk_rw(ATOM, BODY_A, BODY_N),
  close_lvs(BODY_N, FORM).

mk_tree(CTX, _, ID, ntr(ID, SF)) :- 
  atom(ID), !,
  get_assoc(ID, CTX, SF).

mk_tree(CTX, FAS, inference(RUL, _, [ANT]), utr(TREE, HINT, CONC)) :- 
  mk_tree(CTX, FAS, ANT, TREE), 
  tree_conc(TREE, SUB), 
  mk_root(FAS, RUL, SUB, HINT, CONC).

mk_tree(CTX, FAS, inference(RUL, _, [ANT_A, ANT_B]), btr(TREE_A, TREE_B, HINT, CONC)) :- 
  mk_tree(CTX, FAS, ANT_A, TREE_A), 
  tree_conc(TREE_A, CONC_A), 
  mk_tree(CTX, FAS, ANT_B, TREE_B), 
  tree_conc(TREE_B, CONC_B), 
  mk_root(FAS, RUL, CONC_A, CONC_B, HINT, CONC).

/*
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
*/

tuplize(TERM, (ID, TYPE, SF, ANT)) :- 
  (
    TERM =.. [LNG, ID, TYPE, TF, ANT] ;
    TERM =.. [LNG, ID, TYPE, TF, ANT, [_]]
  ), 
  tf_form(LNG, TF, FORM), 
  (
    TYPE = conjecture -> SF = (- FORM) ;
    SF = (+ FORM)
  ).

cperm_aux([], _).
cperm_aux([LIT | LITS_A], LITS_B) :- 
  (
    LIT = $false ;
    LIT = (~ $true) ; 
    LIT = (~ TERM = TERM) ; 
    erient_lit(LIT, EQV),
    member(EQV, LITS_B)
  ), 
  cperm_aux(LITS_A, LITS_B).

cperm(FORM_A, FORM_B) :- 
  inst_fas(FORM_A, BODY_A),
  cf_lits(BODY_A, LITS_A),
  inst_with_pars(0, FORM_B, _, BODY_B), 
  cf_lits(BODY_B, LITS_B),
  cperm_aux(LITS_A, LITS_B).

equiv(SF_A, SF_B) :-
  sf_sign_form(SF_A, SIGN, FORM_A),
  sf_sign_form(SF_B, SIGN, FORM_B), 
  equiv(FORM_A, FORM_B).
equiv(FORM_A, FORM_B) :- 
  uct_break(FORM_A, UCT, SUB_A),
  uct_break(FORM_B, UCT, SUB_B),
  equiv(SUB_A, SUB_B).
equiv(FORM_A, FORM_B) :- 
  bct_break(FORM_A, BCT, SUB_LA, SUB_RA),
  bct_break(FORM_B, BCT, SUB_LB, SUB_RB),
  equiv(SUB_LA, SUB_LB),
  equiv(SUB_RA, SUB_RB).
equiv(FORM, FORM).
equiv(LHS = RHS, RHS = LHS).

entails(SF, SF, rnm).
entails(PREM, CONC, para) :- equiv(PREM, CONC).
entails(+ FORM_A, + FORM_B, eqr) :- cperm(FORM_A, FORM_B).

e_tup_insts(
  _,
  (_, TYPE, _, file(_, _)),
  []
) :- 
  axiomatic(TYPE).

e_tup_insts(
  _,
  (CID, TYPE, SF, PID),
  [inf([parac, dtrx], [PID], CID, SF)]
) :- 
  axiomatic(TYPE),
  atom(PID), !.
  
e_tup_insts(
  CTX,
  (CID, _, SF, ANT),
  INSTS % some(inf([nst(NST)], IDS, ID, SF))
) :- 
  sf_funaris(SF, FAS),
  mk_tree(CTX, FAS, ANT, TREE),
  tree_conc(TREE, CONC), 
  format("Entails? : ~w |= ~w\n\n", [CONC, SF]),
  ( 
    entails(CONC, SF, RUL) -> 
    write("Yes.\n")  
  ;
    write("No.\n"),
    false
  ),
  unroll_tree(0, TREE, SIZE, PID, REV), 
  reverse(REV, PFX),
  mk_dels(SIZE, DELS), 
  append(PFX, [inf([RUL], [PID], CID, SF) | DELS], INSTS).

% unroll_tree(_, _, []).


  % sf_funaris(SF, FAS),
  % ant_insts(CTX, FAS, ANT, 0, TEMP, FI, HYP), 
  % sf_inv(SF, INV),
  % epmt(HYP, (t(FI), INV), (_, 0, 0)),
  % num_pred(FI, PRED),
  % mk_dels(FI, DELS),
  % append(TEMP, [inf(qblx, [t(PRED)], CID, SF) | DELS], INSTS).


% e_tup_inst(
%   (LNG, CID, _, TF, ANT),
%   some(inf([dtrx], [PID], CID, (+ FORM)))
% ) :- 
%   tf_form(LNG, TF, FORM), 
%   e_ant_id(ANT, PID).


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

tup_ctx((ID, _, SF, _), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, SF, CTX_O).

tups_ctx(TUPS, CTX) :- 
  empty_assoc(EMP), 
  foldl(tup_ctx, TUPS, EMP, CTX).

solve(e, _, TSTP, SOL) :- 
  trim_read(TSTP, TEMP), 
  maplist_cut(tuplize, TEMP, TUPS),
  tups_ctx(TUPS, CTX),
  % sorted_ids(TSTP, IDS), 
  % maplist_cut(id_tup, IDS, TUPS), 
  maplist_cut(e_tup_insts(CTX), TUPS, INSTSS),
  append(INSTSS, SOL),
  true.

% solve('metis', PIDS, TSTP, SOL) :- 
%   trim_consult(TSTP),
%   sorted_ids(TSTP, IDS), 
%   maplist_cut(id_tup, IDS, TUPS), 
%   maplist_cut(metis_tuple_inst(PIDS), TUPS, SOL),
%   true.

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