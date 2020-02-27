:- [compile].
:- [wm].
:- [tblx].

tt_term_fv(TT, TERM) :- 
  var(TT) -> 
  TERM = TT ; 
  (
    TT =.. [FUN | TTS], 
    maplist_cut(tt_term_fv, TTS, TERMS), !, 
    TERM = (FUN ^ TERMS)
  ).
 
subst_term(bind(_, $fot(TT)), TERM) :- 
  tt_term_fv(TT, TERM).

m_tuple((fof, ID, TYPE, TF, none)) :- 
  fof(ID, TYPE, TF).

m_tuple((fof, ID, TYPE, TF, RUL)) :- 
  fof(ID, TYPE, TF, RUL).

m_tuple((cnf, ID, TYPE, TF, none)) :- 
  cnf(ID, TYPE, TF).

m_tuple((cnf, ID, TYPE, TF, RUL)) :- 
  cnf(ID, TYPE, TF, RUL).

m_pre_intp(
  (LNG, ID, conjecture, TF, _),
  (LNG, ID, [], TF, cjtr)
).

m_pre_intp(
 (LNG, ID, TYPE, TF, _),
 (LNG, ID, [], TF, axm) 
) :- 
  member(TYPE, [axiom, hypothesis, negated_conjecture]).

m_pre_intp(
  (LNG, ID, plain, TF, inference(subst, [], [PID : SUBSTS])), 
  (LNG, ID, [PID], TF, m_sbst(TERMS)) 
) :- 
  maplist_cut(subst_term, SUBSTS, TERMS).

m_pre_intp(
  (LNG, ID, _, TPTP, inference(RUL, _, IDS)),
  (LNG, ID, IDS, TPTP, TAC)
) :-
  RUL \= subst, 
  m_rul_tac(RUL, TAC).

m_pre_intp(
  (LNG, ID, _, TPTP, introduced(tautology, [refl, _])),
  (LNG, ID, [], TPTP, m_eqr)
). 

m_pre_intp(
  (LNG, ID, _, TPTP, introduced(tautology, [equality, _])),
  (LNG, ID, [], TPTP, m_eq)
). 

m_pre_intp(
  (LNG, ID, _, TPTP, introduced(RUL)),
  (LNG, ID, [], TPTP, TAC) 
) :- 
  RUL \= tautology,
  m_rul_tac(RUL, TAC).

m_rul_tac(strip, m_strp).
m_rul_tac(canonicalize, m_cnn).
m_rul_tac(specialize, m_spc).
m_rul_tac(negate, m_ngt).
m_rul_tac(simplify, m_simp).
m_rul_tac(resolve, res).
m_rul_tac(clausify, m_clsf).
m_rul_tac(conjunct, m_conj).

bind_vars(NUM, [], NUM).
bind_vars(NUM, [#(NUM) | VARS], CNT) :-
  SUCC is NUM + 1,
  bind_vars(SUCC, VARS, CNT).

subgoal_id(ID) :- 
  atom_string(ID, STR),
  string_concat("subgoal_", _, STR).
  
m_intp(TUPLE, (ID, IDS, SF, TAC)) :- 
  m_pre_intp(TUPLE, (LNG, ID, IDS, TF, TAC)),
  tf_form(LNG, TF, FORM),
  (
    (TAC = cjtr ; subgoal_id(ID)) -> 
    SF = (- FORM) ;
    SF = (+ FORM) 
  ).

cnf_form(X, X).

string_id(STR, ID) :- 
  split_string(STR, "(,", " ", [LNG, ID_STR | _]), 
  member(LNG, ["cnf", "fof"]),
  atom_string(ID, ID_STR).

sorted_ids(TSTP, IDS) :-
  file_strings(TSTP, STRS),
  maplist_try(string_id, STRS, IDS).

find_tuple(TUPS, ID, TUP) :- 
  member(TUP, TUPS), 
  TUP = (_, ID, _, _).

m_tstp_hints(TSTP, HINTS) :- 
  trim_consult(TSTP),
  sorted_ids(TSTP, IDS), 
  findall(TUP, m_tuple(TUP), TUPS),
  maplist(find_tuple(TUPS), IDS, SORT_TUPS), 
  maplist_try(m_intp, SORT_TUPS, HINTS).

m_sbst(TERMS, [PREM], CONC, DFP) :- 
  m_sbst_core(TERMS, PREM, CONC, DFP).

m_sbst_core(_, PREM, CONC, DFP) :- 
  many_nb([d], [CONC], DFP, [NEW_CONC], TEMP_DFP), 
  many_nb([c], [PREM], TEMP_DFP, [NEW_PREM], NEW_DFP), 
  ( 
    mate(NEW_PREM, NEW_CONC, NEW_DFP) ;
    prop_tblx(([NEW_PREM, NEW_CONC], NEW_DFP))
  ).

% m_sbst_core([], PREM, CONC, DFP) :-
%   mate(PREM, CONC, DFP).
% 
% m_sbst_core([_ | TERMS], PREM, CONC, DFP) :-
%   i_c(_, PREM, DFP, NEW_PREM, NEW_DFP), 
%   m_sbst_core(TERMS, NEW_PREM, CONC, NEW_DFP).

is_oneq((_, (- _ = _))).
is_opeq((_, (+ _ = _))).

m_eq([], CONC, DFP) :- 
  many_nb([a, d, n], [CONC], DFP, OSFS, TEMP_DFP), 
  partition(is_opeq, OSFS, OPEQS, [ONEQ]), 
  is_oneq(ONEQ), 
  wm(OPEQS, ONEQ, TEMP_DFP).

m_eq([], CONC, DFP) :- 
  many_nb([a, d, n], [CONC], DFP, OSFS, TEMP_DFP), 
  partition(is_opeq, OSFS, OPEQS, [OSF_A, OSF_B]), 
  member(DIR, [l, r]),
  subst_rel_multi(DIR, OSF_A, OPEQS, OSF_B, TEMP_DFP, _). 

m_ngt([PREM], CONC, DFP) :- 
  i_n(CONC, DFP, NEW_CONC, NEW_DFP), 
  mate(PREM, NEW_CONC, NEW_DFP).

m_strp([OPF], ONF, DFP) :- 
  m_strp_core(OPF, ONF, DFP).

m_strp_core(OPF, ONF, DFP) :- 
  (
    i_cd(OPF, ONF, DFP, NEW_OPF, NEW_ONF, NEW_DFP) ;
    i_dc(OPF, ONF, DFP, NEW_OPF, NEW_ONF, NEW_DFP)
  ) ->  
  m_strp_core(NEW_OPF, NEW_ONF, NEW_DFP) ; 
  prop_tblx(([OPF, ONF], DFP)).

m_cnn([PREM], CONC, DFP) :- 
  opqla_onqla(PREM, CONC, DFP) ;
  opqla_onqla(CONC, PREM, DFP).
% 
% m_cnn([PREM], CONC, DFP) :- 
%   para(PREM, CONC, DFP).

m_cnn([PREM], CONC, DFP) :- 
  tblx([PREM], [CONC], DFP).

m_simp_core(PREM, CONC, DFP) :- 
  type_osf(d, CONC) -> 
  (
    many_nb([d], [CONC], DFP, [NEW_CONC], TEMP_DFP), 
    many_nb([c], [PREM], TEMP_DFP, [NEW_PREM], NEW_DFP), 
    prop_tblx(([NEW_PREM, NEW_CONC], NEW_DFP))
  ) ;
  (
    many_nb([d], [PREM], DFP, [NEW_PREM], TEMP_DFP), 
    many_nb([c], [CONC], TEMP_DFP, [NEW_CONC], NEW_DFP), 
    prop_tblx(([NEW_PREM, NEW_CONC], NEW_DFP))
  ).

m_conj([PREM], CONC, DFP) :- 
  many_nb([d], [CONC], DFP, [ONF], DFP0), 
  many_nb([c], [PREM], DFP0, [TEMP_PREM], DFP1), 
  many_nb([a], [TEMP_PREM], DFP1, OPFS, DFP2), 
  member(OPF, OPFS), 
  mate(OPF, ONF, DFP2).

m_eqr([], CONC,  DFP) :- 
  many_nb([d], [CONC], DFP, [TEMP_CONC], TEMP_DFP), 
  eq_refl(TEMP_CONC, TEMP_DFP).

m_clsf([PREM], CONC, DFP) :- 
  opqla_onqla(PREM, CONC, DFP).

m_clsf([PREM], CONC, DFP) :- 
  tblx([PREM], [CONC], DFP).

m_simp([PREM_A, PREM_B], (_, (- $false)), DFP) :- 
  m_simp_core(PREM_A, PREM_B, DFP).

m_simp(PREMS, CONC, DFP) :- 
  CONC \= (_, (- $false)),
  res(PREMS, CONC, DFP).

m_spc([PREM], CONC, DFP) :- 
  mate(PREM, CONC, DFP).

m_add((CID, [], (- Form), cjtr), FIDs, Goal, STRM, [CID | FIDs], NewGoal) :- 
  g_f(Form, Goal, STRM, NewGoal, TempGoal), 
  goal_dfp(TempGoal, DFP), 
  TempGoal = (CTX, _),
  get_prob(0, [CID | FIDs], CTX, PROB), 
  exclude(pos_osf, PROB, OSFS),
  pick_pmt(OSFS, (0, (+ Form)), DFP).

m_add((CID, [], (+ Form), axm), FIDs, Goal, [CID | FIDs], NewGoal) :- 
  g_f(Form, Goal, TempGoal, NewGoal), 
  goal_dfp(TempGoal, DFP), 
  TempGoal = (CTX, _),
  get_prob(0, [CID | FIDs], CTX, PROB), 
  exclude(neg_osf, PROB, OSFS),
  pick_pmt(OSFS, (0, (- Form)), DFP).

m_add(STRM, (CID, PIDs, SF, Tac), FIDs, GOAL, [CID | FIDs], N_GOAL) :- 
  \+ member(Tac, [axm, cjtr]),
  kgs(some(STRM), SF, GOAL, T_GOAL, N_GOAL),
  invert_sf(SF, ISF),
  T_GOAL = (CTX, FP), 
  maplist(fid_osf(CTX, [CID | FIDs]), PIDs, OSFs),
  call(Tac, OSFs, (0, ISF), (0, FP, PRF)), !, 
  ground_all(PRF),
  play_prf(some(STRM), PRF, T_GOAL).

comp_m(TPTP, TSTP, TXTX) :-
  tptp_prob(TPTP, PROB),
  m_tstp_hints(TSTP, HINTS),
  elabs(m_add, HINTS, [], (PROB, 0, PRF)),
  ground(PRF),
  write_file_punct(TXTX, proof(PRF)).