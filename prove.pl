:- [basic].

get_context(PROB, PIDS, CTX) :- 
  maplist(prob_id_hyp(PROB), PIDS, CTX).

pick_mate(HYPS_A, (HYPS_B, GOAL)) :- 
  member(HYP_A, HYPS_A), 
  member(HYP_B, HYPS_B), 
  mate(HYP_A, HYP_B, GOAL).

pick_pivot(HYPS, HYP, GOAL, HYP_N, GOAL_N) :-
  many([b, c, s], ([HYP], GOAL), HGS),
  pluck(HGS, ([HYP_N], GOAL_N), REST), 
  maplist(pick_mate(HYPS), REST). 

apply_aocs(ANTE, [AOC | AOCS], GOAL_I, CONS, GOAL_O) :-  
  many_nb([c], [AOC], GOAL_I, [IMP], GOAL_T), 
  bp(IMP, GOAL_T, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  mate(ANTE, HYP_L, GOAL_L), 
  apply_aocs(HYP_R, AOCS, GOAL_R, CONS, GOAL_O).

apply_aocs(HYP, [], GOAL, HYP, GOAL). 

hyp_mgc((_, (+ FormA)), (_, (- FormB))) :- 
  form_mgc(FormA, FormB).

hyp_mgc((_, (- FormA)), (_, (+ FormB))) :- 
  form_mgc(FormA, FormB).

form_mgc(FormA, FormB) :- 
  unifiable(FormA, FormB, Unif),
  maplist(is_renaming, Unif).
  
form_mgc(TERM_A = TERM_B, FormB) :- 
  unifiable((TERM_B = TERM_A), FormB, Unif),
  maplist(is_renaming, Unif).

is_renaming((X = Y)) :- 
  var(X), 
  \+ var(Y),
  Y = @(NUM),
  number(NUM).

res_aux(HYPS, ([HYP], GOAL)) :- 
  member(CMP, HYPS), 
  hyp_mgc(CMP, HYP),
  mate(CMP, HYP, GOAL).

res(PYP0, PYP1, HYPS, GOAL) :- 
  fp(_, GOAL, NPVT, PPVT, GOAL_N, GOAL_P), 
  many([b, c, s], ([PYP0], GOAL_N), HGS0), 
  many([b, c, s], ([PYP1], GOAL_P), HGS1), !, 
  pluck(HGS0, ([HYP0], GOAL0), REST0), 
  mate_pn(HYP0, NPVT, GOAL0), 
  pluck(HGS1, ([HYP1], GOAL1), REST1), 
  mate_pn(PPVT, HYP1, GOAL1), 
  maplist(pick_mate([NPVT | HYPS]), REST0), 
  maplist(pick_mate([PPVT | HYPS]), REST1). 

eqr_aux(_, ([HYP], GOAL)) :- 
  HYP = (_, (- _ = _)),
  eq_refl(HYP, GOAL).

eqr_aux(HYPS, HG) :- 
  pick_mate(HYPS, HG).

dfu(DEFS, PREM, CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL_T),
  many([b, c, s], ([PREM], GOAL_T), HGS),
  dfu_many(DEFS, HYPS, HGS).

dfu_many([], [], []).

dfu_many(DEFS, HYPS, [HG | HGS]) :- 
  dfu_one(DEFS, HYPS, HG, DEFS_N, HYPS_N),  
  dfu_many(DEFS_N, HYPS_N, HGS).

dfu_one(DEFS, HYPS, ([SRC], GOAL), DEFS_N, HYPS_N) :-  
  pluck(HYPS, TGT, HYPS_N),
  subst_rel_multi(SRC, DEFS, TGT, GOAL, DEFS_N).

dff(_, HYP0, HYP1, DFP) :-
  mate(HYP0, HYP1, DFP). 

dff(Defs, HYP0, HYP1, DFP) :- 
  para_one((HYP0, HYP1, DFP), (NewHYP0, NewHYP1, NewDFP)), !, 
  dff(Defs, NewHYP0, NewHYP1, NewDFP).

dff(Defs, HYP0, HYP1, GOAL) :- 
  para_two((HYP0, HYP1, GOAL), (HYP0L, HYP1L, GOAL_L), (HYP0R, HYP1R, GOAL_R)), 
  dff(Defs, HYP0L, HYP1L, GOAL_L),
  dff(Defs, HYP0R, HYP1R, GOAL_R).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, (+ Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  ap(IFF, l, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Ante, DFP2), 
  dff(Defs, HYP0, Cons, DFP3).

dff(Defs, HYP0, HYP1, DFP) :-
  HYP1 = (_, (- Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  ap(IFF, r, DFP0, IMP, DFP1), 
  bp(IMP, DFP1, Ante, Cons, DFP2, DFP3), 
  mate(HYP1, Cons, DFP3), 
  dff(Defs, HYP0, Ante, DFP2).



%%%%%%%%%%%%%%%% SAT SOLVER %%%%%%%%%%%%%%%% 

lit_num(ANA, ~ ATOM, NEG) :- !,
  get_assoc(ATOM, ANA, NUM), 
  NEG is (- NUM).

lit_num(ANA, ATOM, NUM) :- !,
  get_assoc(ATOM, ANA, NUM).

cla_nums(ANA, CH, NUMS) :- 
  cla_lits(CH, LITS), 
  maplist_cut(lit_num(ANA), LITS, NUMS). 

cla_lits((_, (+ CF)), LITS) :- 
  cf_lits(CF, LITS).

cf_lits(CLA_L | CLA_R, LITS) :- !, 
  cf_lits(CLA_L, LITS_L), 
  cf_lits(CLA_R, LITS_R), 
  append(LITS_L, LITS_R, LITS).
  
cf_lits(LIT, [LIT]). 

cla_atoms(CH, ATOMS) :- 
  cla_lits(CH, LITS),
  maplist_cut(lit_atom, LITS, ATOMS). 

lit_atom(LIT, ATOM) :- 
  LIT = (~ ATOM) -> true ;
  LIT = ATOM.

cla_table(CH, TBL_I, TBL_O) :- 
  cla_atoms(CH, ATOMS), 
  foldl(atom_table, ATOMS, TBL_I, TBL_O).
  
atom_table(ATOM, (NUM_I, ANA_I, NAA_I), TBL_O) :- 
  get_assoc(ATOM, ANA_I, _) -> 
  TBL_O = (NUM_I, ANA_I, NAA_I)
;
  NUM_O is NUM_I + 1, 
  put_assoc(ATOM, ANA_I, NUM_I, ANA_O),
  put_assoc(NUM_I, NAA_I, ATOM, NAA_O),
  TBL_O = (NUM_O, ANA_O, NAA_O).
  
mk_sat_tables(CHS, ANA, NAA) :- 
  empty_assoc(EMP), 
  foldl(cla_table, CHS, (1, EMP, EMP), (_, ANA, NAA)).
  
cla_ctx(CLA, (NUM_I, CTX_I), (NUM_O, CTX_O)) :- 
  NUM_O is NUM_I + 1, 
  put_assoc(NUM_I, CTX_I, CLA, CTX_O).

mk_sat_ctx(CLAS, CTX) :- 
  empty_assoc(EMP), 
  foldl(cla_ctx, CLAS, (1, EMP), (_, CTX)).
  
string_numbers(STR, NUMS) :- 
  split_string(STR, " ", "", STRS), 
  maplist_cut(string_number, STRS, NUMS).

nums_dimacs(NUMS, Str) :- 
  maplist(number_string, NUMS, Strs),
  strings_concat_with(" ", Strs, TempStr),
  string_concat(TempStr, " 0", Str).

num_lit(NAA, NUM, LIT) :- 
  NUM < 0 -> 
  NEG is (- NUM), 
  get_assoc(NEG, NAA, ATOM),
  LIT = (~ ATOM)
;
  get_assoc(NUM, NAA, LIT).

lits_cla([], $false).

lits_cla(Lits, Cla) :- 
  lits_cla_core(Lits, Cla).

lits_cla_core([Lit], Lit).

lits_cla_core([Lit | Lits], Lit | Cla) :- 
  lits_cla_core(Lits, Cla).

nums_cla(NAA, NUMS, CLA) :- 
  maplist_cut(num_lit(NAA), NUMS, LITS),
  lits_cla(LITS, CLA). 

add_del_inst(ID, [del(ID) | SIS], SIS).

line_sat_insts(_, LINE, SIS_I, SIS_O) :- 
  split_string(LINE, " ", "", [_, "d" | NUMS]), 
  append(ID_STRS, ["0"], NUMS), 
  maplist_cut(number_string, IDS, ID_STRS), 
  foldl(add_del_inst, IDS, SIS_I, SIS_O).

line_sat_insts(NAA, LINE, [rup(SIDS, SID, CLA) | SIS], SIS) :- 
  string_numbers(LINE, [SID | NUMS]),
  append(CLA_NUMS, [0 | REST], NUMS), 
  nums_cla(NAA, CLA_NUMS, CLA),
  append(SIDS, [0], REST). 
  
file_sat_insts(NAA, FILE, SIS) :-
  file_strings(FILE, LINES), 
  foldl(line_sat_insts(NAA), LINES, SIS, []).

nums_maxvar(NUMS, MaxVar) :-
  maplist_cut(abs, NUMS, Nats),
  max_list(Nats, MaxVar).

numss_maxvar(NUMSs, MaxVar) :-
  maplist(nums_maxvar, NUMSs, MaxVars),
  max_list(MaxVars, MaxVar).

numss_dimacs(NUMSs, DIMACS) :-
  numss_maxvar(NUMSs, MaxVar), 
  number_string(MaxVar, MaxVarStr),
  length(NUMSs, NumCla),
  number_string(NumCla, NumClaStr),
  strings_concat(["p cnf ", MaxVarStr, " ", NumClaStr], Str),
  maplist(nums_dimacs, NUMSs, Strs),
  strings_concat_with("\n", [Str | Strs], DIMACS).

line_rup(_, LINE, del(SID)) :-
  split_string(LINE, " ", "", ["d", NUM_STR]),
  number_string(SID, NUM_STR).

line_rup(NAA, LINE, rup(SIDS, SID, CLA)) :- 
  string_numbers(LINE, [SID | NUMS]),
  append(CLA_NUMS, [0 | REST], NUMS), 
  nums_cla(NAA, CLA_NUMS, CLA),
  append(SIDS, [0], REST).
  % maplist_cut(sat_get_cla(CTX), IDS, PREMS).

find_new_unit_aux(SAs, SA) :- 
  member(CMP, SAs), 
  complements(CMP, SA).

find_new_unit(CTXSAs, ClaSAs, SA) :- 
  member(SA, ClaSAs), 
  delete(ClaSAs, SA, Rest),
  maplist_cut(find_new_unit_aux(CTXSAs), Rest).

unit_propagate(PREM, (HYPS_I, GOAL_I), ([HYP | HYPS_I], GOAL_O)) :- 
  many([b, s], ([PREM], GOAL_I), HGS), 
  pluck(HGS, ([HYP], GOAL_O), REST),
  maplist_cut(pick_mate(HYPS_I), REST).

get_sat_cla(CTX, SID, CLA) :- 
  get_assoc(SID, CTX, CLA).
  
put_sat_cla(CTX_I, SID, CLA, CTX_O) :- 
  put_assoc(SID, CTX_I, CLA, CTX_O).

del_sat_cla(CTX_I, SID, CLA, CTX_O) :- 
  del_assoc(SID, CTX_I, CLA, CTX_O).

use_sat_inst(CTX, del(SID), GOAL, CTX_N, GOAL_N) :-
  del_sat_cla(CTX, SID, CLA, CTX_N), 
  wp(CLA, GOAL, GOAL_N). 

use_sat_inst(CTX, rup(SIDS, SID, CLA), GOAL, CTX_N, GOAL_N) :- 
  fp(CLA, GOAL, NYP, PYP, GOAL_T, GOAL_N), 
  put_sat_cla(CTX, SID, PYP, CTX_N),
  many_nb([a, s], [NYP], GOAL_T, HYPS_I, GOAL_I), 
  maplist_cut(get_sat_cla(CTX), SIDS, PREMS), !,
  foldl_cut(unit_propagate, PREMS, (HYPS_I, GOAL_I), ([HYP | HYPS_O], GOAL_O)), !,
  member(CMP, HYPS_O),
  mate(HYP, CMP, GOAL_O).

use_sat_insts(CTX, [SI | SIS], GOAL) :- 
  use_sat_inst(CTX, SI, GOAL, CTX_N, GOAL_N), 
  (
    SIS = [] -> 
    SI = rup(_, SID, _), 
    get_sat_cla(CTX_N, SID, CLA), 
    use_pf(CLA, GOAL_N)
  ;
    use_sat_insts(CTX_N, SIS, GOAL_N)
  ).

sat(CLAS, GOAL) :-
  mk_sat_tables(CLAS, ANA, NAA),
  maplist_cut(cla_nums(ANA), CLAS, NUMSS),
  numss_dimacs(NUMSS, DIMACS),
  write_file("temp.cnf", DIMACS), !,
  shell("cadical -q temp.cnf temp.drat", _), !,
  shell("drat-trim temp.cnf temp.drat -L temp.lrat", _), !,
  file_sat_insts(NAA, "temp.lrat", SIS), 
  mk_sat_ctx(CLAS, CTX), 
  use_sat_insts(CTX, SIS, GOAL),
  delete_file("temp.cnf"),
  delete_file("temp.drat"),
  delete_file("temp.lrat").



% %%%%%%%%%%%%%%%% DIRECTED MATRIX %%%%%%%%%%%%%%%%
% 
% dtrx(HYP_L, HYP_R, GOAL) :- 
%   dirixify(l, HYP_L, MAT_L),
%   dirixify(r, HYP_R, MAT_r),
%   empty_assoc(EMP), 
%   solve(MATS, ID_GDS), 
%   term_variables(ID_GDS, VARS),
%   maplist_cut(eq(e), VARS),
%   empty_assoc(EMP), 
%   foldl(add_to_ctx(HYPS), ID_GDS, EMP, CTX), 
%   mtrx((CTX, [], EMP, GOAL)).

%%%%%%%%%%%%%%%% MAIN PROOF COMPILATION %%%%%%%%%%%%%%%%

infer(vampire, ngt, [PREM], CONC, GOAL) :- 
  sp(CONC, GOAL, TEMP, GOAL_T), 
  mate(PREM, TEMP, GOAL_T).

infer(vampire, aft, PREMS, CONC, GOAL) :- 
  tblx([CONC | PREMS], GOAL).

infer(vampire, daft, [PREM], CONC, GOAL) :- 
  tblx(PREM, CONC, GOAL).
  
infer(vampire, dff, [PREM | PREMS], CONC, GOAL) :- 
  sort(PREMS, DEFS),
  dff(DEFS, PREM, CONC, GOAL).

infer(vampire, dfu, [PREM | PREMS], CONC, GOAL) :- 
  dfu(PREMS, PREM, CONC, GOAL).

infer(vampire, sat, PREMS, _, GOAL) :-
  sat(PREMS, GOAL).
  
infer(vampire, pblx, PREMS, CONC, GOAL) :-
  many_nb([a, s], [CONC], GOAL, HYPS, GOAL_T), 
  append(HYPS, PREMS, CLAS),
  pblx(CLAS, GOAL_T).

infer(vampire, gaoc, AOCS, GAOC, GOAL) :- 
  % aoc(PYPs, ONF, GOAL) :- 
  many_nb([d], [GAOC], GOAL, [IMP], GOAL0), 
  IMP = (_, (- (_ => _))),
  aap(IMP, GOAL0, ANTE, CONS, GOAL1), 
  apply_aocs(ANTE, AOCS, GOAL1, TEMP, GOAL2), 
  tblx(TEMP, CONS, GOAL2).
  
infer(vampire, res, [PYP0, PYP1], NYP, GOAL) :- 
  many_nb([a, d, s], [NYP], GOAL, HYPS, GOAL_T), 
  (
    res(PYP0, PYP1, HYPS, GOAL_T) ;
    res(PYP1, PYP0, HYPS, GOAL_T)
  ), !.

infer(vampire, eqr, [PREM], CONC, GOAL) :- 
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL0), 
  many([b, c, s], ([PREM], GOAL0), HGS), !,
  maplist(eqr_aux(HYPS), HGS).

infer(vampire, (sup, DIR), [PREM_A, PREM_B], CONC, GOAL) :- 
  orient_dir(PREM_A, PREM_B, DIR, PREM_L, PREM_R),
  many_nb([a, d, s], [CONC], GOAL, HYPS, GOAL0), 
  pick_pivot(HYPS, PREM_L, GOAL0, SRC, GOAL1), 
  pick_pivot(HYPS, PREM_R, GOAL1, PRE_EQN, GOAL2), 
  PRE_EQN = (_, (+ _ = _)),
  set_dir(PRE_EQN, GOAL2, EQN, GOAL3),
  member_rev(TGT, HYPS),
  subst_rel_single(SRC, EQN, TGT, GOAL3). 

infer(vampire, parac, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  para_cla((PREM, CONC, GOAL)).

infer(vampire, ptrx, PREMS, CONC, GOAL) :- 
  member(PREM, PREMS),
  mtrx([PREM, CONC], GOAL).

infer(vampire, mtrx, PREMS, CONC, GOAL) :- 
  mtrx([CONC | PREMS], GOAL).

infers(PRVR, [TAC | TACS], PREMS, CONC, GOAL) :- 
  infer(PRVR, TAC, PREMS, CONC, GOAL) -> true ;  
  infers(PRVR, TACS, PREMS, CONC, GOAL).

report_failure(PRVR, HINTS, PREMS, CONC, GOAL) :- 
  write("\nInference failed, hints : "), 
  write(HINTS), nl, nl,
  write("\nInference failed, premises :\n\n"),
  write_list(PREMS), 
  format("\nInference failed, conclusion : ~w\n\n", CONC), 
  
  open("debug_trace.pl", write, Stream), 
  write(Stream, ":- [main].\n\n"), 
  format(Stream, '~w.\n\n', debug_prvr(PRVR)), 
  format(Stream, '~w.\n\n', debug_hints(HINTS)), 
  format(Stream, '~w.\n\n', debug_ctx(PREMS)), 
  format(Stream, '~w.\n\n', debug_hyp(CONC)), 
  format(Stream, '~w.\n\n', debug_goal(GOAL)), 
  close(Stream), 
  throw(inference_failure).

% infer(vampire, [hyp], CTX, HYP, GOAL) :- 
%   member(CMP, CTX), 
%   many_nb([d], [HYP], GOAL, [HYP_N], GOAL_T),
%   many_nb([c], [CMP], GOAL_T, [CMP_N], GOAL_N),
%   pmt(CMP_N, HYP_N, GOAL_N) .

prove(STRM, PRVR, [del(PID) | SOL], PROB) :- 
  put_char(STRM, 'W'), 
  put_id(STRM, PID), 
  del_assoc(PID, PROB, _, PROB_N),
  prove(STRM, PRVR, SOL, PROB_N). 

prove(STRM, PRVR, [add(JST, CID, CONC) | SOL], PROB) :- 
  put_char(STRM, 'T'), 
  % write("Justification : "), write(JST), nl,
  % format("Adding axiom : ~w\n", CONC),
  % justified(PROB, CONC, JST),
  % write("Justified.\n\n"),
  put_sf(STRM, CONC), 
  put_atoms(STRM, JST),
  put_id(STRM, CID), 
  put_assoc(CID, PROB, CONC, PROB_N),
  prove(STRM, PRVR, SOL, PROB_N). 

prove(STRM, PRVR, [inf(HINTS, PIDS, CID, - FORM) | SOL], PROB) :- 
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_id(STRM, CID), 
  put_assoc(CID, PROB, - FORM, MAIN_PROB),
  prove(STRM, PRVR, SOL, MAIN_PROB), 
  get_context(PROB, PIDS, CTX),
  GOAL = (PRF, 0, 0),
  timed_call(
    5,
    infers(PRVR, HINTS, CTX, (CID, (+ FORM)), GOAL), 
    report_failure(PRVR, HINTS, CTX, (CID, (+ FORM)), GOAL)
  ), !, 
  ground_all(c, PRF),
  put_assoc(CID, PROB, + FORM, SUB_PROB),
  (
    verify(SUB_PROB, 0, PRF) -> true ;
    throw(verification_failure)
  ),
  put_prf(STRM, PRF).

prove(STRM, PRVR, [inf(HINTS, PIDS, CID, + FORM) | SOL], PROB) :- 
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_id(STRM, CID), 
  get_context(PROB, PIDS, CTX),
  GOAL = (PRF, 0, 0), 
  timed_call(
    5,
    infers(PRVR, HINTS, CTX, (CID, (- FORM)), GOAL), 
    report_failure(PRVR, HINTS, CTX, (CID, (- FORM)), GOAL)
  ), !,
  ground_all(c, PRF),
  put_assoc(CID, PROB, - FORM, SUB_PROB),
  (
    verify(SUB_PROB, 0, PRF) ->  true ; 
    throw(verification_failure)
  ),
  put_prf(STRM, PRF), 
  (
    SOL = [] -> 
    put_prf(STRM, t(- $false, [neg_false], 0, x(CID, 0))) ;
    put_assoc(CID, PROB, + FORM, MAIN_PROB),
    prove(STRM, PRVR, SOL, MAIN_PROB)
  ), !.