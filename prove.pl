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
  
form_mgc(TermA = TermB, FormB) :- 
  unifiable((TermB = TermA), FormB, Unif),
  maplist(is_renaming, Unif).

is_renaming((X = Y)) :- 
  var(X), 
  \+ var(Y),
  Y = @(Num),
  number(Num).

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
  maplist(res_aux([NPVT | HYPS]), REST0), 
  maplist(res_aux([PPVT | HYPS]), REST1). 

infer(vampire, [ngt], [PREM], CONC, GOAL) :- 
  sp(CONC, GOAL, TEMP, GOAL_T), 
  mate(PREM, TEMP, GOAL_T).

infer(vampire, [aft], PREMS, CONC, GOAL) :- 
  tableaux([a, f], [CONC | PREMS], GOAL).

infer(vampire, [pft], PREMS, CONC, GOAL) :-
  tableaux([p, f], [CONC | PREMS], GOAL).

infer(vampire, [daft], [PREM], CONC, GOAL) :- 
  tableaux([d, a, f], PREM, CONC, GOAL).
  
infer(vampire, [pdaft], [PREM], CONC, GOAL) :-
  tableaux([p, d, a, f], PREM, CONC, GOAL).

infer(vampire, [gaoc], AOCS, GAOC, GOAL) :- 
  % aoc(OPFs, ONF, DFP) :- 
  many_nb([d], [GAOC], GOAL, [IMP], GOAL0), 
  IMP = (_, (- (_ => _))),
  aap(IMP, GOAL0, ANTE, CONS, GOAL1), 
  apply_aocs(ANTE, AOCS, GOAL1, TEMP, GOAL2), 
  tableaux([d, a, f], TEMP, CONS, GOAL2).
  
infer(vampire, [res], [PYP0, PYP1], NYP, GOAL) :- 
  many_nb([a, d, s], [NYP], GOAL, HYPS, GOAL_T), 
  (
    res(PYP0, PYP1, HYPS, GOAL_T) ;
    res(PYP1, PYP0, HYPS, GOAL_T)
  ), !.

infer(vampire, [hyp], CTX, HYP, GOAL) :- 
  member(CMP, CTX), 
  tableaux([d, a, f], CMP, HYP, GOAL).

infer(PRVR, HINTS, CTX, HYP, GOAL) :- 
  write("Inference failed, hints : "), 
  write(HINTS), nl, nl,
  open("debug_trace.pl", write, Stream), 
  write(Stream, ":- [main].\n\n"), 
  format(Stream, '~w.\n\n', debug_prvr(PRVR)), 
  format(Stream, '~w.\n\n', debug_hints(HINTS)), 
  format(Stream, '~w.\n\n', debug_ctx(CTX)), 
  format(Stream, '~w.\n\n', debug_hyp(HYP)), 
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
  infer(PRVR, HINTS, CTX, (CID, (+ FORM)), GOAL), !, 
  put_prf(STRM, PRF).

prove(STRM, PRVR, [inf(HINTS, PIDS, CID, + FORM) | SOL], PROB) :- 
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_id(STRM, CID), 
  get_context(PROB, PIDS, CTX),
  GOAL = (PRF, 0, 0), 
  infer(PRVR, HINTS, CTX, (CID, (- FORM)), GOAL), !, 
  put_assoc(CID, PROB, - FORM, SUB_PROB),
  verify(SUB_PROB, 0, PRF),
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

mk_mono(Num, Cons, ! ! ((#(1) = #(0)) => Mono)) :-
  num_pred(Num, Pred), 
  mk_mono(Pred, Cons, Mono), !.

mk_mono_args(0, [], []).

mk_mono_args(Num, [#(NumA) | VarsA], [#(NumB) | VarsB]) :-
  NumA is (Num * 2) - 1, 
  NumB is (Num * 2) - 2, 
  Pred is Num - 1,
  mk_mono_args(Pred, VarsA, VarsB).

mk_mono_eq(Num, Fun, TERM_A = TERM_B) :- 
  mk_mono_args(Num, VarsA, VarsB),
  TERM_A =.. [Fun | VarsA],
  TERM_B =.. [Fun | VarsB], !.

mk_mono_imp(Num, Rel, AtomA => AtomB) :- 
  mk_mono_args(Num, VarsA, VarsB),
  AtomA =.. [Rel | VarsA],
  AtomB =.. [Rel | VarsB], !.

mk_mono_fun(Num, Fun, Mono) :- 
  mk_mono_eq(Num, Fun, Eq), 
  mk_mono(Num, Eq, Mono), !.

mk_mono_rel(Num, Rel, Mono) :- 
  mk_mono_imp(Num, Rel, Imp), 
  mk_mono(Num, Imp, Mono).



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