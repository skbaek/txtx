:- [basic].


get_context(PROB, PIDS, CTX) :- 
  maplist(prob_id_hyp(PROB), PIDS, CTX).

/*
pmt_a_aux(HYP, GOAL, HYP_L, HYP_R, GOAL_N) :- 
  \+ imp_HYP(HYP), 
  ap(l, HYP, GOAL, HYP_L, TEMP_GOAL),
  ap(r, HYP, TEMP_GOAL, HYP_R, NEW_GOAL).

pmt_a(HYP, GOAL, HYPS, NEW_GOAL) :- 
  pmt_a_aux(HYP, GOAL, HYP_L, HYP_R, GOAL0) -> 
  (
    pmt_a(HYP_L, GOAL0, HYPS_L, GOAL1),
    pmt_a(HYP_R, GOAL1, HYPS_R, NEW_GOAL), 
    append(HYPS_L, HYPS_R, HYPS)
  ) ;
  (HYPS = [HYP], NEW_GOAL = GOAL).

pmt_b(HYP, GOAL, OGOALS) :- 
  (
    \+ imp_HYP(HYP),
    bp(HYP, GOAL, HYP_L, GOAL_L, HYP_R, GOAL_R)
  ) -> 
  (
    pmt_b(HYP_L, GOAL_L, OGOALS_L),
    pmt_b(HYP_R, GOAL_R, OGOALS_R),
    append(OGOALS_L, OGOALS_R, OGOALS)
  ) ;
  OGOALS = [([HYP], GOAL)].

pmt_l([], []).

pmt_l(HYPS, [([HYP1], GOAL) | OGOALS]) :- 
  pluck(HYPS, HYP0, REST), 
  pmt(HYP0, HYP1, GOAL), 
  pmt_l(REST, OGOALS).

pmt_r([], []).

pmt_r(HYPS, [([HYP1], GOAL) | OGOALS]) :- 
  pluck(HYPS, HYP0, REST), 
  pmt(HYP1, HYP0, GOAL), 
  pmt_r(REST, OGOALS).

pmt(HYP0, HYP1, GOAL) :- 
  mate(HYP0, HYP1, GOAL).

pmt(HYP0, HYP1, GOAL) :- 
  para_step(HYP0, HYP1, GOAL, NewHYP0, NewHYP1, NewGOAL), !, 
  pmt(NewHYP0, NewHYP1, NewGOAL).

pmt(HYP_A, HYP_B, GOAL) :- 
  imp_HYP(HYP_A),
  abp(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R), !,
  pmt(HYP_AL, HYP_BL, GOAL_L), !, 
  pmt(HYP_AR, HYP_BR, GOAL_R), !. 

pmt(HYP_A, HYP_B, GOAL) :- 
  imp_HYP(HYP_B),
  bap(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R), !,
  pmt(HYP_AL, HYP_BL, GOAL_L), !,
  pmt(HYP_AR, HYP_BR, GOAL_R), !. 

pmt(HYP0, HYP1, GOAL) :- 
  \+ imp_HYP(HYP0),
  type_HYP(a, HYP0),
  pmt_a(HYP0, GOAL, HYPs, GOAL_T), !,  
  pmt_b(HYP1, GOAL_T, OGOALs), 
  pmt_l(HYPs, OGOALs).

pmt(HYP0, HYP1, GOAL) :- 
  \+ imp_HYP(HYP1),
  type_HYP(a, HYP1),
  pmt_a(HYP1, GOAL, HYPs, GOAL_T), !,  
  pmt_b(HYP0, GOAL_T, OGOALs), 
  pmt_r(HYPs, OGOALs).

imp_HYP(HYP) :- 
  HYP = (_, SF),
  sf_form(SF, FORM),
  member(FORM, [(_ => _), (_ <=> _)]).

sf_form(+ Form, Form).
sf_form(- Form, Form).
*/

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
  % unify_with_occurs_check(TERM_A, TERM_B),
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

% cla_nums(ANA, CLA_L | CLA_R, NUMS) :- !, 
%   cla_nums(ANA, CLA_L, NUMS_L),
%   cla_nums(ANA, CLA_R, NUMS_R),
%   append(NUMS_L, NUMS_R, NUMS).
% 
% cla_atoms(~ ATOM, [ATOM]) :- !. 
% 
% cla_atoms(LIT, [LIT]). 

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

/*

%%%%%%%%%%%%%%%% MATRIX TABLEAUX %%%%%%%%%%%%%%%%

matrixify(VARS, (FI, SF), (FO, a(MAT_L, MAT_R))) :-
  aab(SF, SF_L, SF_R), !,
  matrixify(VARS, (FI, SF_L), (FT, MAT_L)),
  matrixify(VARS, (FT, SF_R), (FO, MAT_R)).

matrixify(VARS, (FI, SF), (FO, b(MAT_L, MAT_R))) :- 
  bb(SF, SF_L, SF_R), !,
  matrixify(VARS, (FI, SF_L), (FT, MAT_L)),
  matrixify(VARS, (FT, SF_R), (FO, MAT_R)).

matrixify(VARS, (FI, SF), (FO, c(VAR, MAT))) :- 
  cb(VAR, SF, SF_N), !,
  matrixify([VAR | VARS], (FI, SF_N), (FO, MAT)). 

matrixify(VARS, (FI, SF), (FO, d(SKM, MAT))) :- 
  type_sf(d, SF), !,
  atom_concat(skm, FI, SKM), 
  FT is FI + 1, 
  SKM_TERM =.. [SKM | VARS],
  dt(SKM_TERM, SF, SF_N), 
  matrixify(VARS, (FT, SF_N), (FO, MAT)). 

matrixify(VARS, (FI, SF), (FO, MAT)) :- 
  sb(SF, SF_N), !,
  matrixify(VARS, (FI, SF_N), (FO, MAT)). 

matrixify(_, (FI, SA), (FI, SA)) :- 
  signed_atom(SA).

get_id_gd(MATS, ID, (ID, GD)) :- 
  get_assoc(ID, MATS, (GD, _)).

startable(a(MAT_L, MAT_R)) :- 
  startable(MAT_L) ;
  startable(MAT_R).

startable(b(MAT_L, MAT_R)) :- 
  startable(MAT_L),
  startable(MAT_R).

startable(c(_, MAT)) :- startable(MAT).
startable(d(_, MAT)) :- startable(MAT).
startable(+ _). 

solve(MATS, ID_GDS) :- 
  pluck_assoc(ID, MATS, (GD, MAT), REST), 
  solve(start, 0, REST, [], [], (GD, MAT), _, IDS), 
  maplist_cut(get_id_gd(MATS), [ID | IDS], ID_GDS).

solve(MODE, FI, MATS, PATH, LEM_I, (a(GD_L, GD_R), a(MAT_L, MAT_R)), LEM_O, IDS) :- !, 
  FI_N is FI + 1, 
  atom_concat(t, FI, TID),
  (
    put_assoc(TID, MATS, (GD_R, MAT_R), MATS_N), 
    solve(MODE, FI_N, MATS_N, PATH, LEM_I, (GD_L, MAT_L), LEM_O, IDS) 
  ;
    put_assoc(TID, MATS, (GD_L, MAT_L), MATS_N), 
    solve(MODE, FI_N, MATS_N, PATH, LEM_I, (GD_R, MAT_R), LEM_O, IDS) 
  ).

solve(start, FI, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O, IDS) :- !,
  startable(MAT_R),
  solve(start, FI, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T, IDS_L),
  solve(start, FI, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O, IDS_R),
  union(IDS_L, IDS_R, IDS).

solve(match, FI, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O, IDS) :- !,
  (
    solve(match, FI, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T, IDS_L),
    solve(block, FI, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O, IDS_R),
    union(IDS_L, IDS_R, IDS)
  ;
    solve(match, FI, MATS, PATH, LEM_I, (GD_R, MAT_R), LEM_T, IDS_R),
    solve(block, FI, MATS, PATH, LEM_T, (GD_L, MAT_L), LEM_O, IDS_L),
    union(IDS_L, IDS_R, IDS)
  ).
  
solve(block, FI, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O, IDS) :- !,
  solve(block, FI, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T, IDS_L),
  solve(block, FI, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O, IDS_R),
  union(IDS_L, IDS_R, IDS).

solve(MODE, FI, MATS, PATH, LEM_I, (c(TERM, GD), c(TERM, MAT)), LEM_O, IDS) :- !,
  solve(MODE, FI, MATS, PATH, LEM_I, (GD, MAT), LEM_O, IDS). 

solve(MODE, FI, MATS, PATH, LEM_I, (d(SKM, GD), d(SKM, MAT)), LEM_O, IDS) :- !,
  solve(MODE, FI, MATS, PATH, LEM_I, (GD, MAT), LEM_O, IDS). 

solve(match, _, _, [CMP | _], LEM, (m, SA), LEM, []) :- 
  connect_sfs(CMP, SA).
  
solve(start, FI, MATS, PATH, LEM_I, (GD, SF), LEM_O, IDS) :-
  pos_atom(SF), 
  solve(block, FI, MATS, PATH, LEM_I, (GD, SF), LEM_O, IDS).

solve(block, _, _, _, LEM, (c, SF), LEM, []) :-
  contradiction(SF).

solve(block, _, _, _, LEM, (m, SA), LEM, []) :- 
  member_syn(SA, LEM), !.

solve(block, _, _, PATH, LEM, (m, SA), LEM, []) :- 
  member(CMP, PATH),
  connect_sfs(CMP, SA).

solve(block, FI, MATS, PATH, LEM, (m, SA), [SA | LEM], IDS) :- 
  \+ member_syn(SA, PATH),
  pluck_assoc(ID, MATS, (GD, MAT), REST), 
  (
    atom_concat(t, _, ID) -> IDS = TEMP ;
    IDS = [ID | TEMP]
  ),
  solve(match, FI, REST, [SA | PATH], LEM, (GD, MAT), _, TEMP). 
 
add_to_ctx(HYPS, (ID, GD), CTX_I, CTX_O) :- 
  member((ID, SF), HYPS), 
  put_assoc(ID, CTX_I, (GD, SF), CTX_O).

mtrx_zero((CTX, _, _, GOAL)) :- 
  gen_mh(CTX, (c, HYP)), 
  use_lc(HYP, GOAL).
  
mtrx_zero((CTX, PATH, _, GOAL)) :- 
  gen_mh(CTX, (m, HYP)), 
  member(CMP, PATH), 
  mate(HYP, CMP, GOAL).

mtrx_one((CTX, PATH, SKMS, GOAL), MS) :- 
  gen_mh(CTX, (GD, HYP)), 
  (
    atomic_hyp(HYP) -> 
    GD = m,
    del_mh(HYP, CTX, CTX_N),
    MS = (CTX_N, [HYP | PATH], SKMS, GOAL)
  ;
    sp(HYP, GOAL, HYP_N, GOAL_N) ->
    del_mh(HYP, CTX, CTX_T),
    put_mh((GD, HYP_N), CTX_T, CTX_N),
    MS = (CTX_N, PATH, SKMS, GOAL_N)
  ;
    GD = a(GD_L, GD_R) -> 
    del_mh(HYP, CTX, CTX_T),
    add_if_not_end(CTX_T, HYP, GOAL, GD_L, l, CTX0, GOAL0),
    add_if_not_end(CTX0, HYP, GOAL0, GD_R, r, CTX1, GOAL1),
    MS = (CTX1, PATH, SKMS, GOAL1)
  ;
    GD = c(TERM, GD_S) -> 
    replace_skm(SKMS, TERM, TERM_N), 
    del_mh(HYP, CTX, CTX_T),
    cp(HYP, TERM_N, GOAL, HYP_N, GOAL_N), 
    put_mh((GD_S, HYP_N), CTX_T, CTX_N),
    MS = (CTX_N, PATH, SKMS, GOAL_N)
  ;
    GD = d(SKM, GD_S) -> 
    del_mh(HYP, CTX, CTX_T),
    GOAL = (_, FP, _), 
    put_assoc(SKM, SKMS, FP, SKMS_N), 
    dp(HYP, GOAL, HYP_N, GOAL_N), 
    put_mh((GD_S, HYP_N), CTX_T, CTX_N),
    MS = (CTX_N, PATH, SKMS_N, GOAL_N)
  ).

replace_skm(SKMS, TERM_I, TERM_O) :- 
  var(TERM_I) -> false 
; 
  TERM_I = (FUN ^ TERMS_I), 
  (
    atom_concat(skm, _, FUN) -> 
    get_assoc(FUN, SKMS, NUM), 
    TERM_O = @(NUM)
  ;  
    maplist_cut(replace_skm(SKMS), TERMS_I, TERMS_O), 
    TERM_O = (FUN ^ TERMS_O)
  ).

add_if_not_end(CTX, _, GOAL, e, _, CTX, GOAL) :- !.

add_if_not_end(CTX, HYP, GOAL, GD, DIR, CTX_N, GOAL_N) :- 
  ap(HYP, DIR, GOAL, HYP_N, GOAL_N), 
  put_mh((GD, HYP_N), CTX, CTX_N).
  
gen_mh(CTX, (GD, ID, SF)) :- 
  gen_assoc(ID, CTX, (GD, SF)). 
  
del_mh((ID, SF), CTX_I, CTX_O) :- 
  del_assoc(ID, CTX_I, (_, SF), CTX_O).

put_mh((GD, ID, SF), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, (GD, SF), CTX_O).
   
mtrx_two(
  (CTX, PATH, SKMS, GOAL), 
  (GD_L, HYP_L), 
  (CTX_T, PATH, SKMS, GOAL_L), 
  (GD_R, HYP_R), 
  (CTX_T, PATH, SKMS, GOAL_R) 
) :- 
  gen_mh(CTX, (b(GD_L, GD_R), HYP)), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R),
  del_mh(HYP, CTX, CTX_T).

mtrx_fcs(
  (GD, HYP), 
  (CTX, PATH, SKMS, GOAL)
) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R) -> 
  GD = b(GD_L, GD_R), 
  mtrx_fcs((GD_L, HYP_L), (CTX, PATH, SKMS, GOAL_L)), !,
  mtrx_fcs((GD_R, HYP_R), (CTX, PATH, SKMS, GOAL_R))
;
  put_mh((GD, HYP), CTX, CTX_N),
  mtrx((CTX_N, PATH, SKMS, GOAL)).

mtrx(MS) :- 
  mtrx_zero(MS) -> true ; 
  mtrx_one(MS, MS_N) -> mtrx(MS_N) ; 
  mtrx_two(MS, MH_L, MS_L, MH_R, MS_R),
  mtrx_fcs(MH_L, MS_L), !, 
  mtrx_fcs(MH_R, MS_R), !. 

add_mat((ID, SF), (FI, MATS_I), (FO, MATS_O)) :- 
  matrixify([], (FI, SF), (FO, MAT)), 
  put_assoc(ID, MATS_I, (_, MAT), MATS_O).

matrixify_all(HYPS, MATS) :- 
  empty_assoc(EMP), 
  foldl(add_mat, HYPS, (0, EMP), (_, MATS)).

mtrx(HYPS, GOAL) :- 
  matrixify_all(HYPS, MATS),
  solve(MATS, ID_GDS), 
  term_variables(ID_GDS, VARS),
  maplist_cut(eq(e), VARS),
  empty_assoc(EMP), 
  foldl(add_to_ctx(HYPS), ID_GDS, EMP, CTX), 
  mtrx((CTX, [], EMP, GOAL)).

*/



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
  ground_all(c^[], PRF),
  % put_assoc(CID, PROB, + FORM, SUB_PROB),
  % (
  %   verify(SUB_PROB, 0, PRF) -> true ;
  %   throw(verification_failure)
  % ),
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
  ground_all(c^[], PRF),
  % put_assoc(CID, PROB, - FORM, SUB_PROB),
  % (
  %   verify(SUB_PROB, 0, PRF) ->  true ; 
  %   throw(verification_failure)
  % ),
  put_prf(STRM, PRF), 
  (
    SOL = [] -> 
    put_prf(STRM, t(- $false, [neg_false], 0, x(CID, 0))) ;
    put_assoc(CID, PROB, + FORM, MAIN_PROB),
    prove(STRM, PRVR, SOL, MAIN_PROB)
  ), !.

/* 
%%%%%%%% BASIC INFERENCES %%%%%%%%

id_of_sa(GOAL, ID) :- 
  hyp(GOAL, ID, SA),
  signed_atom(SA).

signed_atom(Satom) :- pos_atom(Satom).
signed_atom(Satom) :- neg_atom(Satom).
neg_atom(- ATOM) :- unsigned_atom(ATOM).
pos_atom(+ ATOM) :- unsigned_atom(ATOM).
unsigned_atom(ATOM) :- \+ molecular(ATOM).

ap(
  PID, 
  DIR, 
  (PROB, a(PID, DIR, FID, PRF), FP, FID), 
  FID, 
  (PROB_N, PRF, FP, FID_N)
) :- 
  get_assoc(PID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(FID, PROB, CONC, PROB_N),
  FID_N is FID + 1.

bp(
  PID,
  (PROB, b(PID, FID, PRF_L, PRF_R), FP, FID), 
  FID,
  (PROB_L, PRF_L, FP, FID_N),
  (PROB_R, PRF_R, FP, FID_N)
) :- 
  get_assoc(PID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R), 
  put_assoc(FID, PROB, CONC_L, PROB_L),
  put_assoc(FID, PROB, CONC_R, PROB_R),
  FID_N is FID + 1.
   
cp(
  PID,
  TERM, 
  (PROB, c(PID, TERM, FID, PRF), FP, FID), 
  FID,
  (PROB_N, PRF, FP, FID_N)
) :- 
  get_assoc(PID, PROB, PREM),
  cb(TERM, PREM, CONC),
  put_assoc(FID, PROB, CONC, PROB_N),
  FID_N is FID + 1.

dp(
  PID, 
  (PROB, d(PID, FID, PRF), FP, FID), 
  FID,
  (PROB_N, PRF, FP_N, FID_N)
) :-
  get_assoc(PID, PROB, PREM),
  db(FP, PREM, CONC),
  put_assoc(FID, PROB, CONC, PROB_N),
  FP_N is FP + 1, 
  FID_N is FID + 1.

fp(
  FORM,
  (f(FORM, FID, PRF_L, PRF_R), FP, FID), 
  FID,
  (PROB_L, PRF_L, FP, FID_N), 
  (PROB_R, PRF_R, FP, FID_N)
) :-
  put_assoc(FID, PROB, - FORM, PROB_L),
  put_assoc(FID, PROB, + FORM, PROB_R),
  FID_N is FID + 1.

tp(
  SF,
  JST,
  (PROB, t(SF, JST, FID, PRF), FP, FID),
  FID, 
  (PROB_N, PRF, FP, FID_N)
) :- 
  put_assoc(FID, PROB, SF, PROB_N),
  FID_N is FID + 1.

sp(
  PID,
  (PROB, s(PID, CID, PRF), FP, FI), 
  CID,
  (PROB_N, PRF, FP, FI)
) :- 
  get_assoc(PID, PROB, PREM),
  sb(PREM, CONC),
  put_assoc(CID, PROB, CONC, PROB_N).

wp(
  PID, 
  (PROB, w(PID, PRF), FP, FI), 
  (PROB_N, PRF, FP, FI)
) :- 
  del_assoc(PID, PROB, _, PROB_N).

xp(
  PID, 
  NID, 
  (PROB, x(PID, NID), _, _)
) :-
  get_assoc(PID, PROB, + FORM_P), 
  get_assoc(NID, PROB, - FORM_N), 
  unify_with_occurs_check(FORM_P, FORM_N).

aap(PID, GOAL, LID, RID, GOAL_N) :- 
  ap(PID, l, GOAL, LID, GOAL_T), 
  ap(PID, r, GOAL_T, RID,  GOAL_N).

fps(+ FORM, GOAL, CID, GOAL_N, GOAL_P) :- 
  fp(FORM, GOAL, CID, GOAL_N, GOAL_P).

fps(- FORM, GOAL, CID, GOAL_P, GOAL_N) :- 
  fp(FORM, GOAL, CID, GOAL_N, GOAL_P).

val_lookup(VAL, NUM, (NUM, TERM)) :- 
  member((NUM, TERM), VAL).

vi_in(VI, EXP) :- 
  sub_term($(VI), EXP), 
  number(VI).

orient(PID, NID, l, PID, NID) :- 
  hyp(PID, + _),
  hyp(NID, - _).

orient(NID, PID, r, PID, NID) :- 
  hyp(PID, + _),
  hyp(NID, - _).

set_dir(PID, GOAL, PID, GOAL). 

set_dir(PID, GOAL, CID, GOAL_N) :- 
  hyp(PID, + (TERM_A = TERM_B)), 
  fp(TERM_B = TERM_A, GOAL, CID, GOAL_T, GOAL_N), 
  eq_symm(PID, CID, GOAL_T), !. 

mate_pf(PID, GOAL) :- 
  hyp(PID, + $false),
  tp(- $false, [neg_false], GOAL, NID, GOAL_T),
  xp(PID, NID, GOAL_T).

mate_nt(NID, GOAL) :- 
  hyp(NID, - $true),
  tp(+ $true, [pos_true], GOAL, PID, GOAL_T),
  xp(PID, NID, GOAL_T).

mate_tf(HYP, GOAL) :- 
  mate_nt(HYP, GOAL) ;
  mate_pf(HYP, GOAL).

mate_nu(HYP0, HYP1, GOAL) :- 
  mate_tf(HYP0, GOAL) ;
  mate_tf(HYP1, GOAL).

mate_nu(HYP0, HYP1, GOAL) :- 
  orient(HYP0, HYP1, _, OPF, ONF),
  mate_pn_nu(OPF, ONF, GOAL).

mate(HYP_L, HYP_R, GOAL) :- 
  mate_tf(HYP_L, GOAL) ;
  mate_tf(HYP_R, GOAL).

mate(HYP0, HYP1, GOAL) :- 
  orient(HYP0, HYP1, _, OPF, ONF),
  mate_pn(OPF, ONF, GOAL).

mate_pn(OPF, ONF, GOAL) :- 
  set_dir(OPF, GOAL, NewOPF, NewGOAL), 
  xp(NewOPF, ONF, NewGOAL).

mate_pn_nu(PRE_PID, NID, GOAL) :- 
  set_dir(PRE_PID, GOAL, PID, GOAL_T), 
  hyp(PID, (+ FORM)),
  hyp(NID, (- FORM)),
  xp(PID, NID, GOAL_T).

id_rnm(PID, NID) :- 
  hyp(PID, + FORM_P), 
  hyp(NID, - FORM_N), 
  form_rnm(FORM_P, FORM_N).

id_rnm(NID, PID) :- 
  hyp(PID, + FORM_P), 
  hyp(NID, - FORM_N), 
  form_rnm(FORM_P, FORM_N).

term_rnm(#(NUM), #(NUM)).
term_rnm(@(NUM), @(NUM)).
term_rnm($(_), @(_)).
term_rnm(TERM_A, TERM_B) :- 
  TERM_A = [FUN | TERMS_A],
  TERM_B = [FUN | TERMS_B],
  maplist_cut(term_rnm, TERMS_A, TERMS_B).

form_rnm(FORM_A, FORM_B) :- 
  FORM_A = [UCT, SUB_A], 
  FORM_B = [UCT, SUB_B], 
  uct(UCT), !, 
  form_rnm(SUB_A, SUB_B).

form_rnm(FORM_A, FORM_B) :- 
  FORM_A = [BCT, SUB_AL, SUB_AR], 
  FORM_B = [BCT, SUB_BL, SUB_BR], 
  bct(BCT), !, 
  form_rnm(SUB_AL, SUB_BL),
  form_rnm(SUB_AR, SUB_BR).

form_rnm(FORM_A, FORM_B) :- 
  FORM_A = [REL | TERMS_A],
  FORM_B = [REL | TERMS_B],
  maplist_cut(term_rnm, TERMS_A, TERMS_B).
  
form_rnm(TERM_A = TERM_B, TERM_C = TERM_D) :- 
  term_rnm(TERM_A, TERM_D),
  term_rnm(TERM_B, TERM_C).

pivot_aux(HYPs, ([HYP1], GOAL)) :- 
  member(HYP0, HYPs), 
  id_rnm(HYP0, HYP1),
  mate(HYP0, HYP1, GOAL).

pivot_isa(OSA, HYPs, HYP, GOAL) :- 
  many([b, c, s], ([HYP], GOAL), OGOALs), 
  pluck(OGOALs, ([NewHYP], NewGOAL), Rest),
  mate(OSA, NewHYP, NewGOAL), 
  maplist(pivot_aux([OSA | HYPs]), Rest).

many(RULS, (PIDS, GOAL), PAIRS) :-
  member(s, RULS), 
  pluck(PIDS, PID, REST), 
  sp(PID, GOAL, NID, GOAL_N), !,
  many(RULS, ([NID | REST], GOAL_N), PAIRS).

many(RULS, (PIDS, GOAL), PAIRS) :-
  member(a, RULS), 
  pluck(PIDS, PID, REST), 
  aap(PID, GOAL, LID, RID, GOAL_N), !, 
  many(RULS, ([LID, RID | REST], GOAL_N), PAIRS).

many(RULS, (PIDS, GOAL), PAIRS) :-
  member(d, RULS), 
  pluck(PIDS, PID, REST), 
  dp(PID, GOAL, NID, GOAL_N), !,
  many(RULS, ([NID | REST], GOAL_N), PAIRS).

many(RULS, (PIDS, GOAL), PAIRS) :-
  member(c, RULS), 
  pluck(PIDS, PID, REST), 
  cp(PID, GOAL, _, NID, GOAL_N), !,
  many(RULS, ([NID | REST], GOAL_N), PAIRS).

many(RULS, (PIDS, GOAL), PAIRS) :-
  member(b, RULS), 
  pluck(PIDS, PID, REST), 
  bp(PID, GOAL, CID, GOAL_L, GOAL_R), !, 
  many(RULS, ([CID | REST], GOAL_L), PAIRS_L), !,
  many(RULS, ([CID | REST], GOAL_R), PAIRS_R), !,
  append(PAIRS_L, PAIRS_R, PAIRS), !.

many(_, PAIR, [PAIR]).

many_nb(RULS, ISFs, IPP, NewISFs, NewIPP) :-
  many(RULS, (ISFs, IPP), [(NewISFs, NewIPP)]).

qla_sas(SF, SAs) :- 
  cb(_, SF, NewSF), 
  qla_sas(NewSF, SAs).

qla_sas(SF, SAs) :- 
  sb(SF, NewSF), 
  qla_sas(NewSF, SAs).

qla_sas(SF, SAs) :- 
  bb(SF, SF0, SF1), 
  qla_sas(SF0, SAs0),
  qla_sas(SF1, SAs1),
  append(SAs0, SAs1, SAs).

qla_sas(SF, [SF]) :- 
  signed_atom(SF).

res(PID0, PID1, CID, GOAL) :- 
 many_nb([a, d, s], [CID], GOAL, IDS, GOAL_T), !, 
 hyp(PID1, PF1), 
 qla_sas(PF1, SAS),
 member(SA, SAS),
 fps(SA, GOAL_T, CID, GOAL_L, GOAL_R), 
 pivot_isa(CID, IDS, PID0, GOAL_R), 
 pivot_isa(CID, IDS, PID1, GOAL_L). 



%%%%%%%% Tableaux %%%%%%%% 

bad_inst(TERM, FP) :- 
  sub_term(SUB_TERM, TERM), 
  ground(SUB_TERM),
  SUB_TERM = @(NUM),
  FP =< NUM.

% Check that a term used for gamma rule instantiation 
% 
check_inst((TERM, FP)) :- 
  \+ bad_inst(TERM, FP).

pick_la(TS, LA, N_TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  pluck(LFS, LA, REST), 
  id_of_sa(GOAL, LA),
  N_TS = (TERMS, LAS, REST, RFS, RAS, GOAL).

pick_ra(TS, RA, N_TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  pluck(RFS, RA, REST),
  id_of_sa(GOAL, RA),
  N_TS = (TERMS, LAS, LFS, REST, RAS, GOAL).

inv_step(HYPS, GOAL, [HYP_A, HYP_B | REST], N_GOAL) :- 
  pluck(HYPS, HYP, REST),
  aap(HYP, GOAL, HYP_A, HYP_B, N_GOAL).

inv_step(HYPS, GOAL, [N_HYP | REST], N_GOAL) :- 
  pluck(HYPS, HYP, REST),
  (
    sp(HYP, GOAL, N_HYP, N_GOAL) ;
    dp(HYP, GOAL, N_HYP, N_GOAL)
  ).

inv_step(
  (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  (TERMS, LAS, N_LFS, RFS, RAS, N_GOAL)
) :- 
  inv_step(LFS, GOAL, N_LFS, N_GOAL).

inv_step(
  (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  (TERMS, LAS, LFS, N_RFS, RAS, N_GOAL)
) :- 
  inv_step(RFS, GOAL, N_RFS, N_GOAL).

pick_mate_nu(
  (_, _, LFS, _, RAS, GOAL) 
) :- 
  member(LA, LFS), 
  id_of_sa(GOAL, LA), 
  member(RA, RAS), 
  mate_nu(LA, RA, GOAL).

pick_mate_nu(
  (_, LAS, _, RFS, _, GOAL) 
) :- 
  member(RA, RFS), 
  id_of_sa(GOAL, RA), 
  member(LA, LAS), 
  mate_nu(LA, RA, GOAL).

tblx0(TS) :- 
  inv_step(TS, N_TS) -> tblx0(N_TS) ;
  pick_mate_nu(TS) -> true ;
  tblx1(TS).

tblx1(TS) :- 
  pick_la(TS, LA, N_TS) -> tblx1(l, LA, N_TS) ; 
  pick_ra(TS, RA, N_TS) -> tblx1(r, RA, N_TS) ; 
  tblx2(TS).

tblx1(l, LA, TS) :- 
  TS = (INSTS, _, _, _, RAS, GOAL), 
  member(RA, RAS), 
  mate(LA, RA, GOAL), 
  maplist_cut(check_inst, INSTS).

tblx1(l, LA, TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  tblx0((TERMS, [LA | LAS], LFS, RFS, RAS, GOAL)). 

tblx1(r, RA, TS) :- 
  TS = (INSTS, LAS, _, _, _, GOAL), 
  member(LA, LAS), 
  mate(LA, RA, GOAL),
  maplist_cut(check_inst, INSTS).

tblx1(r, RA, TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, GOAL), 
  tblx0((TERMS, LAS, LFS, RFS, [RA | RAS], GOAL)). 

tblx2((TERMS, LAS, LFS, RFS, RAS, GOAL)) :- 
  pluck(LFS, LF, REST),
  bp(LF, GOAL, LF0, GOAL0, GOAL1), 
  tblx0((TERMS, LAS, [LF0 | REST], RFS, RAS, GOAL0)), 
  tblx0((TERMS, LAS, [LF0 | REST], RFS, RAS, GOAL1)). 

tblx2((TERMS, LAS, LFS, RFS, RAS, GOAL)) :- 
  pluck(RFS, RF, REST),
  bp(RF, GOAL, RF0, GOAL0, GOAL1), 
  tblx0((TERMS, LAS, LFS, [RF0 | REST], RAS, GOAL0)), 
  tblx0((TERMS, LAS, LFS, [RF0 | REST], RAS, GOAL1)). 

tblx2((INSTS, LAS, LFS, RFS, RAS, GOAL)) :- 
  GOAL = (_, FP, _),
  pluck(LFS, LF, REST),
  cp(LF, TERM, GOAL, N_LF, N_GOAL), 
  tblx0(([(TERM, FP) | INSTS], LAS, [N_LF | REST], RFS, RAS, N_GOAL)). 

tblx2((INSTS, LAS, LFS, RFS, RAS, GOAL)) :- 
  GOAL = (_, FP, _),
  pluck(RFS, RF, REST),
  cp(RF, TERM, GOAL, N_RF, N_GOAL), 
  tblx0(([(TERM, FP) | INSTS], LAS, LFS, [N_RF | REST], RAS, N_GOAL)).

tblx(HYPS_A, HYPS_B, GOAL) :- 
  tblx0(([], [], HYPS_A, HYPS_B, [], GOAL)). 



%%%%%%% Equality %%%%%%% 

% eq_symm(TERM, GOAL)
% --- 
% GOAL := ... |- PID : Term = Term, ...
eq_refl(ONF, IPP) :- 
  ONF = (_, (- (Term = Term))),
  tp(+ ! (#(0) = #(0)), [refl_eq], IPP, ISF0, TempIPP), 
  cp(ISF0, Term, TempIPP, IPF, NewIPP), 
  xp(IPF, ONF, NewIPP).

hyp((PROB, _, _, _), ID, SF) :- 
  get_assoc(ID, PROB, SF).

% eq_symm(TERM_A, TERM_B, GOAL)
% --- 
% GOAL ::= PID : TERM_A = TERM_B, ... |- NID : TERM_B = TERM_A, ...
% IPF = PID + TERM_A = TERM_B
% INF = NID - TERM_B = TERM_A
eq_symm(PID, NID, GOAL) :- 
  hyp(GOAL, PID, (+ TERM_A = TERM_B)), 
  hyp(GOAL, NID, (- TERM_B = TERM_A)), 
  tp(+ ! ! ((#(1) = #(0)) => (#(0) = #(1))), [symm_eq], GOAL, ID0, GOAL0), 
  cp(GOAL0, TERM_A, ID0, ID1, GOAL1), 
  cp(ID1, TERM_B, GOAL1, ID2, GOAL2), 
  bp(ID2, GOAL2, ID3, GOAL3, GOAL4), 
  mate_pn(PID, ID3, GOAL3), 
  mate_pn(ID3, NID, GOAL4). 

eq_symm(PID, GOAL, CID, GOAL_N) :- 
  hyp(PID, GOAL, + TERM_A = TERM_B), 
  fp(TERM_B = TERM_A, GOAL, CID, GOAL_T, GOAL_N), 
  eq_symm(PID, CID, GOAL_T).

% eq_trans(TERM_A, TERM_B, TERM_C, GOAL)
% --- 
% GOAL := PID0 : TERM_A = TERM_B, PID1 : TERM_B = TERM_C, ... |- CID : TERM_A = TERM_C, ...
% IPF0 = PID0 + TERM_A = TERM_B
% IPF1 = PID1 + TERM_B = TERM_C
% INF = NID - TERM_A = TERM_C
eq_trans(PID0, PID1, NID, GOAL) :- 
  hyp(PID0, GOAL, + (TERM_A = TERM_B)), !,
  hyp(PID1, GOAL, + (TERM_B = TERM_C)), !,
  hyp(NID, GOAL, - (TERM_A = TERM_C)), !,
  tp(+ ! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0)))), [trans_eq], GOAL, MONO0, GOAL0),  !,
  cp(MONO0, TERM_A, GOAL0, MONO1, GOAL1), !,
  cp(MONO1, TERM_B, GOAL1, MONO2, GOAL2), !,
  cp(MONO2, TERM_C, GOAL2, MONO3, GOAL3), !,
  bp(MONO3, GOAL3, MONO4, GOAL4, GOAL5), !,
  mate(PID0, MONO4, GOAL4), !,
  bp(MONO4, GOAL5, MONO5, GOAL6, GOAL7), !,
  mate(PID1, MONO5, GOAL6), !,
  mate(NID, MONO5, GOAL7), !.

subst_fun_multi(IPES, INE, PFF, IPES_N) :-
  INE = (_, (- (TERM_A = TERM_B))), 
  (
    TERM_A == TERM_B -> 
    eq_refl(INE, PFF), 
    IPES_N = IPES ;
    subst_fun_multi_aux(IPES, INE, PFF, IPES_N)
  ).

subst_fun_multi_aux(IPES, INE, PFF, IPES) :- 
  INE = (_, (- (TERM_A = TERM_B))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(INE, PFF).

subst_fun_multi_aux(IPES, INE, PFF, IPES_N) :-
  break_eq_fun(IPES, INE, PFF, EPS),
  subst_fun_multi_many(IPES, EPS, IPES_N). 

subst_fun_multi_aux(PIDS, NID, GOAL, PIDS_N) :- 
  hyp(GOAL, NID, - (TERM_A0 = TERM_C)), 
  pluck_unique(PIDS, PID, REST),
  many_nb([c], [PID], GOAL, [PID0], GOAL0), 
  set_dir(PID0, GOAL0, PID1, GOAL1), 
  hyp(GOAL, PID1, + TERM_A1 = TERM_B),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL1, CID, GOAL2, GOAL3), 
  subst_fun_multi(REST, CID, GOAL2, PIDS_N), 
  eq_trans(PID1, CID, NID, GOAL3).

subst_fun_multi_many(OPEs, [], OPEs).

subst_fun_multi_many(IPES, [(INE, PFF) | EPS], IPES_N) :-
  subst_fun_multi(IPES, INE, PFF, IPES_T),
  subst_fun_multi_many(IPES_T, EPS, IPES_N).

subst_rel_multi(ISF_A, IPES, ISF_B, PFF, IPES_N) :-  
  orient(ISF_A, ISF_B, _, PRE_IPA, INA),
  set_dir(PRE_IPA, PFF, IPA, PFF_T),
  break_eq_rel(IPES, IPA, INA, PFF_T, EPS),
  subst_fun_multi_many(IPES, EPS, IPES_N). 

intro_eqs([], [], MONO, PFF, [], MONO, PFF).

intro_eqs([TERM_A | TERMS_A], [TERM_B | TERMS_B], MONO, GOAL, [(CID, GOAL_S) | EPS], CONC, GOAL_N) :-
  cp(MONO, TERM_A, GOAL, MONO_A, GOAL_A), 
  cp(MONO_A, TERM_B, GOAL_A, MONO_AB, GOAL_AB), 
  bp(MONO_AB, GOAL_AB, CID, GOAL_S, GOAL_T), 
  intro_eqs(TERMS_A, TERMS_B, CID, GOAL_T, EPS, CONC, GOAL_N). 

break_eq_fun(IPES, INE, PFF, EPS) :- 
  INE = (_, (- TERM_A = TERM_B)),
  % \+ var(TERM_A),
  % \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(possibly_eq(IPES), TERMS_A, TERMS_B),
  mk_mono_fun(LTH, FUN, MONO_FORM),
  atom_number(LTH_ATOM, LTH),
  tp(+ MONO_FORM, [mono_fun, FUN, LTH_ATOM], PFF, MONO, PFF0),
  intro_eqs(TERMS_A, TERMS_B, MONO, PFF0, EPS, IPE, PFF1),
  xp(IPE, INE, PFF1).

break_eq_rel(IPES, IPA, INA, PFF, EPS) :- 
  IPA = (_, (+ ATOM_A)),
  INA = (_, (- ATOM_B)),
  ATOM_A =.. [REL | TERMS_A], 
  ATOM_B =.. [REL | TERMS_B], 
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(possibly_eq(IPES), TERMS_A, TERMS_B),
  mk_mono_rel(LTH, REL, MONO_FORM),
  atom_number(LTH_ATOM, LTH),
  tp(+ MONO_FORM, [mono_rel, REL, LTH_ATOM], PFF, MONO, PFF0),
  intro_eqs(TERMS_A, TERMS_B, MONO, PFF0, EPS, CONC, PFF1),
  bp(CONC, PFF1, CID, PFF_L, PFF_R), 
  xp(IPA, CID, PFF_L), 
  xp(CID, INA, PFF_R). 

possibly_eq(TERM_A, TERM_B) :- 
  TERM_A = #(_) -> false ;
  TERM_B = #(_) -> false ;
  TERM_A = $(_) -> true ;
  TERM_B = $(_) -> true ;
  (
    TERM_A = @(NUM), 
    TERM_B = @(NUM)
  ) -> true ; 
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, Lth),
  length(TERMS_B, Lth).

possibly_eq(_, TERM_A, TERM_B) :- 
  possibly_eq(TERM_A, TERM_B).

possibly_eq(IPES, TERM_A, TERM_B) :- 
  member((_, (+ EQ)), IPES), 
  inst_fas(EQ, TERM_L = TERM_R), 
  ( 
    possibly_eq(TERM_A, TERM_L) ; 
    possibly_eq(TERM_A, TERM_R) ; 
    possibly_eq(TERM_B, TERM_R) ; 
    possibly_eq(TERM_B, TERM_L) 
  ).

inst_fas(FORM, BODY) :-
  FORM = (! _) ->
  subst_form(_, FORM, FORM_T),
  inst_fas(FORM_T, BODY) ; 
  BODY = FORM.

mk_mono(0, Cons, Cons).

mk_mono(NUM, Cons, ! ! ((#(1) = #(0)) => Mono)) :-
  num_pred(NUM, Pred), 
  mk_mono(Pred, Cons, Mono), !.

mk_mono_args(0, [], []).

mk_mono_args(NUM, [#(NUMA) | VarsA], [#(NUMB) | VarsB]) :-
  NUMA is (NUM * 2) - 1, 
  NUMB is (NUM * 2) - 2, 
  Pred is NUM - 1,
  mk_mono_args(Pred, VarsA, VarsB).

mk_mono_eq(NUM, Fun, TERM_A = TERM_B) :- 
  mk_mono_args(NUM, VarsA, VarsB),
  TERM_A =.. [Fun | VarsA],
  TERM_B =.. [Fun | VarsB], !.

mk_mono_imp(NUM, Rel, AtomA => AtomB) :- 
  mk_mono_args(NUM, VarsA, VarsB),
  AtomA =.. [Rel | VarsA],
  AtomB =.. [Rel | VarsB], !.

mk_mono_fun(NUM, Fun, Mono) :- 
  mk_mono_eq(NUM, Fun, Eq), 
  mk_mono(NUM, Eq, Mono), !.

mk_mono_rel(NUM, Rel, Mono) :- 
  mk_mono_imp(NUM, Rel, Imp), 
  mk_mono(NUM, Imp, Mono).



%%%%%%%% MAIN %%%%%%%%

% tptx_prob(TPTX, [HYP | HYPS]) :- 
%   open(TPTX, read, STRM, [encoding(octet)]),
%   get_list(STRM, get_hyp, [HYP | HYPS]),
%   close(STRM).

write_prf(PATH, PRF) :- 
  open(PATH, write, STRM, [encoding(octet)]),
  put_prf(STRM, PRF),
  close(STRM).

trd((_, _, X), X).

infer([metis, hyp], PIDS, CID, GOAL) :- 
  member(PID, PIDS), 
  mate(PID, CID, GOAL).

infer([metis, res], [PID_A, PID_B], CID, GOAL) :- 
  res(PID_A, PID_B, CID, GOAL).

infer([metis, subst], [PID], CID, GOAL) :- 
  tblx([PID], [CID], GOAL).

% prove([metis, eq], [], HYP, PFF) :- 
%   many_nb([d], [HYP], PFF, [HYP0], PFF0),
%   aap(HYP0, PFF0, HYP_L0, HYP1, PFF1), 
%   sp(HYP_L0, PFF1, HYP_L1, PFF2), 
%   aap(HYP1, PFF2, HYP_R0, HYP2, PFF3), 
%   sp(HYP_R0, PFF3, HYP_R1, PFF4), 
%   (
%     subst_rel_multi(HYP_R1, [HYP_L1], HYP2, PFF4, _) ; 
%     subst_rel_multi(HYP_L1, [HYP_R1], HYP2, PFF4, _) 
%   ).
% 
% prove([metis, refl], [], HYP, GOAL) :- 
%   many_nb([d], [HYP], GOAL, [HYP0], GOAL0),
%   eq_refl(HYP0, GOAL0).

orig_hyp(ID - _) :-
  atom_concat(p, _, ID).

add_hyp(PROB, ID, PROB_IN, PROB_OUT) :- 
  get_assoc(ID, PROB, SF), 
  put_assoc(ID, PROB_IN, SF, PROB_OUT).

pair_key(X - _, X).

swap(GOAL, X, Y, Z) :- 
  call(GOAL, Y, X, Z).

get_context(PROB, orig, CTX) :- !,
  assoc_to_list(PROB, HYPS), 
  include(orig_hyp, HYPS, ORIG_HYPS),
  maplist_cut(pair_key, ORIG_HYPS, PIDS),
  list_to_assoc(ORIG_HYPS, CTX).

get_context(PROB, PIDS, CTX) :- 
  maplist(swap(get_assoc, PROB), PIDS, CTX).
  
*/