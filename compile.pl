:- [rules].

literal(~ Atom) :- 
  \+ molecular(Atom).

literal(Atom) :- 
  \+ molecular(Atom).

pred_def_norm(! Xs : TPTP, ! Xs : NewTPTP) :- 
  pred_def_norm(TPTP, NewTPTP).

pred_def_norm((TPTP | ~ Atom), (Atom <=> TPTP)).
pred_def_norm((Atom <=> TPTP), (Atom <=> TPTP)).

eq(X, X).

ground_all(Term) :- 
  term_variables(Term, Vars),
  maplist_cut(eq((c ^ [])), Vars).

i_aa(OSF, DFP, OSF_L, OSF_R, NewDFP) :- 
  i_a(l, OSF, DFP, OSF_L, TempDFP), 
  i_a(r, OSF, TempDFP, OSF_R, NewDFP). 

i_ab(OSF_A, OSF_B, DFP, OSF_AL, OSF_BL, DFP_L, OSF_AR, OSF_BR, DFP_R) :- 
  i_b(OSF_B, DFP, OSF_BL, TempDFP_L, OSF_BR, TempDFP_R), 
  i_a(l, OSF_A, TempDFP_L, OSF_AL, DFP_L),
  i_a(r, OSF_A, TempDFP_R, OSF_AR, DFP_R).

i_ab_cf(OSF_A, OSF_B, DFP, OSF_AR, OSF_BL, DFP_L, OSF_AL, OSF_BR, DFP_R) :- 
  i_b(OSF_B, DFP, OSF_BL, TempDFP_L, OSF_BR, TempDFP_R), 
  i_a(r, OSF_A, TempDFP_L, OSF_AR, DFP_L),
  i_a(l, OSF_A, TempDFP_R, OSF_AL, DFP_R).

i_ab_sw(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) :- 
  i_ab(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) ;
  i_ab_cf(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B).

i_ba(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) :- 
  i_ab(OSF1, OSF0, DFP, OSF1A, OSF0A, DFP_A, OSF1B, OSF0B, DFP_B). 

i_ba_cf(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) :- 
  i_ab_cf(OSF1, OSF0, DFP, OSF1A, OSF0A, DFP_A, OSF1B, OSF0B, DFP_B). 

i_ba_sw(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) :- 
  i_ba(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B) ;
  i_ba_cf(OSF0, OSF1, DFP, OSF0A, OSF1A, DFP_A, OSF0B, OSF1B, DFP_B).

i_f_s(+ Form, DFP, ONF, DFP_N, OPF, DFP_P) :- 
  i_f(Form, DFP, ONF, DFP_N, OPF, DFP_P).

i_f_s(- Form, DFP, OPF, DFP_P, ONF, DFP_N) :- 
  i_f(Form, DFP, ONF, DFP_N, OPF, DFP_P).

i_cd(OSF_C, OSF_D, DFP, NewOSF_C, NewOSF_D, NewDFP) :- 
  DFP = (_, FP, _), 
  i_d(OSF_D, DFP, NewOSF_D, TempDFP), 
  i_c(@(FP), OSF_C, TempDFP, NewOSF_C, NewDFP). 

i_dc(OSF0, OSF1, DFP, NEW_OSF0, NEW_OSF1, NEW_DFP) :- 
  i_cd(OSF1, OSF0, DFP, NEW_OSF1, NEW_OSF0, NEW_DFP).

g_f_s((+ FORM), GOAL, SUB_GOAL, MAIN_GOAL) :- 
  g_f(FORM, GOAL, SUB_GOAL, MAIN_GOAL).

g_f_s((- FORM), GOAL, SUB_GOAL, MAIN_GOAL) :- 
  g_f(FORM, GOAL, MAIN_GOAL, SUB_GOAL).

many(Rules, (ISFs, IPP), IIPPs) :-
  member(n, Rules), 
  pluck(ISFs, ISF, Rest), 
  i_n(ISF, IPP, NewISF, NewIPP), !,
  many(Rules, ([NewISF | Rest], NewIPP), IIPPs).

many(Rules, (ISFs, IPP), IIPPs) :-
  member(a, Rules), 
  pluck(ISFs, ISF, Rest), 
  i_a(l, ISF, IPP, ISF_L, TempIPP), 
  i_a(r, ISF, TempIPP, ISF_R, NewIPP), !, 
  many(Rules, ([ISF_R, ISF_L | Rest], NewIPP), IIPPs).

many(Rules, (ISFs, IPP), IIPPs) :-
  member(d, Rules), 
  pluck(ISFs, ISF, Rest), 
  i_d(ISF, IPP, NewISF, NewIPP), !,
  many(Rules, ([NewISF | Rest], NewIPP), IIPPs).

many(Rules, (ISFs, IPP), IIPPs) :-
  member(c, Rules), 
  pluck(ISFs, ISF, Rest), 
  i_c(_, ISF, IPP, NewISF, NewIPP), !,
  many(Rules, ([NewISF | Rest], NewIPP), IIPPs).

many(Rules, (ISFs, IPP), IIPPs) :-
  member(b, Rules), 
  pluck(ISFs, ISF, Rest), 
  i_b(ISF, IPP, ISF_L, IPP_L, ISF_R, IPP_R), !, 
  many(Rules, ([ISF_L | Rest], IPP_L), IIPPsL), !,
  many(Rules, ([ISF_R | Rest], IPP_R), IIPPsR),
  append(IIPPsL, IIPPsR, IIPPs). 

many(_, IIPP, [IIPP]).

many_nb(Rules, ISFs, IPP, NewISFs, NewIPP) :-
  many(Rules, (ISFs, IPP), [(NewISFs, NewIPP)]).

mate_pf(OPF, DFP) :- 
  OPF = (_, (+ $false)),
  i_h(- $false, neg_false, DFP, ONF, NewDFP),
  i_x(OPF, ONF, NewDFP).

mate_nt(ONF, DFP) :- 
  ONF = (_, (- $true)),
  i_h(+ $true, pos_true, DFP, OPF, NewDFP),
  i_x(OPF, ONF, NewDFP).

mate_tf(OSF, DFP) :- 
  mate_nt(OSF, DFP) ;
  mate_pf(OSF, DFP).

mate_nu(OSF0, OSF1, DFP) :- 
  mate_tf(OSF0, DFP) ;
  mate_tf(OSF1, DFP).

mate_nu(OSF0, OSF1, DFP) :- 
  orient(OSF0, OSF1, _, OPF, ONF),
  mate_pn_nu(OPF, ONF, DFP).

mate(OSF_L, OSF_R, DFP) :- 
  mate_tf(OSF_L, DFP) ;
  mate_tf(OSF_R, DFP).

mate(OSF0, OSF1, DFP) :- 
  orient(OSF0, OSF1, _, OPF, ONF),
  mate_pn(OPF, ONF, DFP).

mate_pn(OPF, ONF, DFP) :- 
  set_dir(OPF, DFP, NewOPF, NewDFP), 
  i_x(NewOPF, ONF, NewDFP).

mate_pn_nu(OPF, ONF, DFP) :- 
  set_dir(OPF, DFP, N_OPF, N_DFP), 
  N_OPF = (_, (+ FORM_A)),
  ONF = (_, (- FORM_B)),
  unifiable(FORM_A, FORM_B, []), 
  i_x(N_OPF, ONF, N_DFP).

rev_dir(OPF, DFP, NewOPF, NewDFP) :- 
  OPF = (_, (+ (TermA = TermB))), 
  i_f(TermB = TermA, DFP, NewONF, TempDFP, NewOPF, NewDFP), 
  eq_symm(OPF, NewONF, TempDFP), !. 
 
set_dir(OPF, DFP, OPF, DFP).
set_dir(OPF, DFP, NewOPF, NewDFP) :- 
  rev_dir(OPF, DFP, NewOPF, NewDFP).



%%%%%%% Equality Axiom Application %%%%%%% 

% eq_symm(Term, Goal)
% --- 
% Goal := ... |- PID : Term = Term, ...
eq_refl(ONF, IPP) :- 
  ONF = (_, (- (Term = Term))),
  i_h(+ ! (#(0) = #(0)), refl_eq, IPP, ISF0, TempIPP), 
  i_c(Term, ISF0, TempIPP, IPF, NewIPP), 
  i_x(IPF, ONF, NewIPP).

% eq_symm(TermA, TermB, Goal)
% --- 
% Goal ::= PID : TermA = TermB, ... |- NID : TermB = TermA, ...
% IPF = PID + TermA = TermB
% INF = NID - TermB = TermA
eq_symm(OPF, ONF, DFP) :- 
  OPF = (_, (+ (TermA = TermB))), 
  ONF = (_, (- (TermB = TermA))),
  i_h(+ ! ! ((#(1) = #(0)) => (#(0) = #(1))), symm_eq, DFP, ISF0, IPP0), 
  i_c(TermA, ISF0, IPP0, ISF1, IPP1), 
  i_c(TermB, ISF1, IPP1, ISF2, IPP2), 
  i_b(ISF2, IPP2, ISF3, IPP3, ISF4, IPP4), 
  mate_pn(OPF, ISF3, IPP3), 
  mate_pn(ISF4, ONF, IPP4). 

eq_symm(OPF, DFP, NewOPF, NewDFP) :- 
  OPF = (_, (+ TermA = TermB)), 
  i_f(TermB = TermA, DFP, ONF, TempDFP, NewOPF, NewDFP), 
  eq_symm(OPF, ONF, TempDFP).

% eq_trans(TermA, TermB, TermC, Goal)
% --- 
% Goal := PID0 : TermA = TermB, PID1 : TermB = TermC, ... |- CID : TermA = TermC, ...
% IPF0 = PID0 + TermA = TermB
% IPF1 = PID1 + TermB = TermC
% INF = NID - TermA = TermC
eq_trans(IPF0, IPF1, INF, IPP) :- 
  IPF0 = (_, (+ (TermA = TermB))), !,
  IPF1 = (_, (+ (TermB = TermC))), !,
  INF = (_, (- (TermA = TermC))), !,
  i_h(+ ! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0)))), trans_eq, IPP, Mono0, IPP0),  !,
  i_c(TermA, Mono0, IPP0, Mono1, IPP1), !,
  i_c(TermB, Mono1, IPP1, Mono2, IPP2), !,
  i_c(TermC, Mono2, IPP2, Mono3, IPP3), !,
  i_b(Mono3, IPP3, Mono4, IPP4, Mono5, IPP5), !,
  mate(IPF0, Mono4, IPP4), !,
  i_b(Mono5, IPP5, Mono6, IPP6, Mono7, IPP7), !,
  mate(IPF1, Mono6, IPP6), !,
  mate(INF, Mono7, IPP7), !.



%%%%%%% Decomposition to Equational Goals %%%%%%%

intro_eqs(Mono, [], [], DFP, Mono, [], DFP).

intro_eqs(Mono, [TermA | TermsA], [TermB | TermsB], DFP, Iff, [(ONE, SubDFP) | ODFPs], NewDFP) :-
  i_c(TermA, Mono, DFP, MonoA, DFP_A), 
  i_c(TermB, MonoA, DFP_A, MonoAB, DFP_AB), 
  i_b(MonoAB, DFP_AB, ONE, SubDFP, TempMono, TempDFP), 
  intro_eqs(TempMono, TermsA, TermsB, TempDFP, Iff, ODFPs, NewDFP). 

%break_eq_fun_aux(ONE, Mono, [], [], DFP, []) :- 
%  mate(ONE, Mono, DFP).
%
%break_eq_fun_aux(ONEq, Mono, [TermA | TermsA], [TermB |TermsB], DFP, [(NewONEq, NewDFP) | EDFPs]) :- 
%  i_c(TermA, Mono, DFP, MonoA, DFP_A), 
%  i_c(TermB, MonoA, DFP_A, MonoAB, DFP_AB), 
%  i_b(MonoAB, DFP_AB, NewONEq, NewDFP, TempMono, TempDFP), 
%  break_eq_fun_aux(ONEq, TempMono, TermsA, TermsB, TempDFP, EDFPs). 

break_eq_fun(OPEs, ONE, DFP, ODFPs) :- 
  ONE = (_, (- TermA = TermB)),
  \+ var(TermA),
  \+ var(TermB),
  TermA = (Fun ^ TermsA),
  TermB = (Fun ^ TermsB),
  length(TermsA, Lth),
  length(TermsB, Lth),
  maplist_cut(term_poseq_term(OPEs), TermsA, TermsB),
  mk_mono_fun(Lth, Fun, MonoForm),
  i_h(+ MonoForm, mono_fun(Fun, Lth), DFP, Mono, DFP0),
  intro_eqs(Mono, TermsA, TermsB, DFP0, OPE, ODFPs, DFP1),
  i_x(OPE, ONE, DFP1).

break_eq_rel(Dir, OPEs, OPA, ONA, DFP, ODFPs) :- 
  OPA = (_, (+ AtomA)),
  ONA = (_, (- AtomB)),
  AtomA =.. [Rel | TermsA], 
  AtomB =.. [Rel | TermsB], 
  length(TermsA, Lth),
  length(TermsB, Lth),
  ( 
    Dir = l -> 
    maplist_cut(term_poseq_term(OPEs), TermsA, TermsB) ;
    maplist_cut(term_poseq_term(OPEs), TermsB, TermsA) 
  ),
  mk_mono_rel(Lth, Rel, MonoForm),
  i_h(+ MonoForm, mono_rel(Rel, Lth), DFP, Mono, DFP0),
  ( 
    (
      Dir = l, 
      intro_eqs(Mono, TermsA, TermsB, DFP0, Iff, ODFPs, DFP1),
      i_a(l, Iff, DFP1, Imp, DFP2)
    ) ;
    (
      Dir = r, 
      intro_eqs(Mono, TermsB, TermsA, DFP0, Iff, ODFPs, DFP1),
      i_a(r, Iff, DFP1, Imp, DFP2)
    ) 
  ),
  i_b(Imp, DFP2, OSF_L, DFP_L, OSF_R, DFP_R), 
  i_x(OPA, OSF_L, DFP_L), 
  i_x(OSF_R, ONA, DFP_R). 



%%%%%%% Substitution Axiom Application %%%%%%%

subst_fun_single(OPE, (ONE, DFP)) :- 
  subst_fun_single(OPE, ONE, DFP). 

subst_fun_single(OPE, ONE, DFP) :-
  ONE = (_, (- (TermA = TermB))), 
  (
    TermA == TermB -> 
    eq_refl(ONE, DFP) ;
    subst_fun_single_0(OPE, ONE, DFP)
  ).

subst_fun_single_0(OPE, ONE, DFP) :-
  OPE = (_, (+ FormA)), 
  ONE = (_, (- FormB)), 
  (
    FormA == FormB ->  
    i_x(OPE, ONE, DFP) ;
    subst_fun_single_1(OPE, ONE, DFP)
  ).

subst_fun_single_1(_, ONE, DFP) :-
  ONE = (_, (- (TermA = TermB))), 
  unify_with_occurs_check(TermA, TermB),
  eq_refl(ONE, DFP).

subst_fun_single_1(OPE, ONE, DFP) :-
  i_x(OPE, ONE, DFP).

subst_fun_single_1(OPE, ONE, DFP) :-
  break_eq_fun([OPE], ONE, DFP, ODFPs),
  maplist(subst_fun_single(OPE), ODFPs). 

subst_fun_multi(OPEs, ONE, DFP, NewOPEs) :-
  ONE = (_, (- (TermA = TermB))), 
  (
    TermA == TermB -> 
    (eq_refl(ONE, DFP), NewOPEs = OPEs) ;
    subst_fun_multi_0(OPEs, ONE, DFP, NewOPEs)
  ).

subst_fun_multi_0(OPEs, ONF, DFP, OPEs) :- 
  ONF = (_, (- (TermA = TermB))), 
  unify_with_occurs_check(TermA, TermB),
  eq_refl(ONF, DFP).

subst_fun_multi_0(OPEs, ONE, DFP, NewOPEs) :-
  break_eq_fun(OPEs, ONE, DFP, ODFPs),
  subst_fun_multi_aux(OPEs, ODFPs, NewOPEs). 

subst_fun_multi_0(OPQEs, ONE, DFP, NewOPQEs) :- 
  ONE = (_, (- (TermA0 = TermC))), 
  pluck_uniq(OPQEs, OPQE, Rest),
  many_nb([c], [OPQE], DFP, [OPE], DFP0), 
  OPE = (_, (+ TermA1 = TermB)),
  unify_with_occurs_check(TermA0, TermA1), 
  i_f(TermB = TermC, DFP0, NewONE, DFP1, NewOPE, DFP2), 
  subst_fun_multi(Rest, NewONE, DFP1, NewOPQEs), 
  eq_trans(OPE, NewOPE, ONE, DFP2).

subst_fun_multi_aux(OPEs, [], OPEs).

subst_fun_multi_aux(OPEs, [(ONE, DFP) | ODFPs], NewOPEs) :-
  subst_fun_multi(OPEs, ONE, DFP, TempOPEs),
  subst_fun_multi_aux(TempOPEs, ODFPs, NewOPEs).
  
subst_rel_multi(DirA, OSF_L, OPEs, OSF_R, DFP, NewOPEs) :-  
  orient(OSF_L, OSF_R, DirB, PreOPA, ONA),
  dir_iff(DirA, DirB, Dir),
  set_dir(PreOPA, DFP, OPA, TempDFP),
  break_eq_rel(Dir, OPEs, OPA, ONA, TempDFP, ODFPs),
  subst_fun_multi_aux(OPEs, ODFPs, NewOPEs). 

subst_rel_single(OSF_L, OPE, OSF_R, DFP) :-  
  orient(OSF_L, OSF_R, Dir, PreOPA, ONA),
  set_dir(PreOPA, DFP, OPA, TempDFP),
  break_eq_rel(Dir, [OPE], OPA, ONA, TempDFP, ODFPs),
  maplist(subst_fun_single(OPE), ODFPs).

%%%%%%%% Rule-specific tactics %%%%%%%%

tfe([OPF], ONF, DFP) :- 
  tfe_core(OPF, ONF, DFP). 

tfe_type(+ $true, x).
tfe_type(+ $false, x).
tfe_type(- $true, x).
tfe_type(- $false, x).

tfe_type(+ _ | $true, x).
tfe_type(+ $true | _, x).
tfe_type(+ _ | $false, b).
tfe_type(+ $false | _, b).

tfe_type(+ _ & $true, al).
tfe_type(+ _ & $false, ar).
tfe_type(+ $true & _, ar).
tfe_type(+ $false & _, al).

tfe_type(+ _ => $true, x).
tfe_type(+ _ => $false, b).
tfe_type(+ $true => _, b).
tfe_type(+ $false => _, x).

tfe_type(+ _ <=> $false, al).
tfe_type(+ $true <=> _, al).
tfe_type(+ _ <=> $true, ar).
tfe_type(+ $false <=> _, ar).

tfe_type(- _ | $true, ar).
tfe_type(- $true | _, al).
tfe_type(- _ | $false, al).
tfe_type(- $false | _, ar).

tfe_type(- _ & $true, b).
tfe_type(- _ & $false, x).
tfe_type(- $true & _, b).
tfe_type(- $false & _, x).

tfe_type(- _ => $true, ar).
tfe_type(- _ => $false, al).
tfe_type(- $true => _, ar).
tfe_type(- $false => _, al).

tfe_type(- _ <=> $false, b).
tfe_type(- $true <=> _, b).
tfe_type(- _ <=> $true, b).
tfe_type(- $false <=> _, b).

tfe_core(OSF0, OSF1, DFP) :-
  i_x(OSF0, OSF1, DFP) ;
  i_x(OSF1, OSF0, DFP).

tfe_core(OSF0, OSF1, DFP) :-
  OSF0 = (_, SF0),
  tfe_type(SF0, x), !,
  mate(OSF0, OSF1, DFP).

tfe_core(SRC, TGT, DFP) :-
  SRC = (_, SF),
  tfe_type(SF, al), 
  i_a(l, SRC, DFP, NewSRC, NewDFP), !, 
  tfe_core(NewSRC, TGT, NewDFP), !.

tfe_core(SRC, TGT, DFP) :-
  SRC = (_, SF),
  tfe_type(SF, ar), 
  i_a(r, SRC, DFP, NewSRC, NewDFP), !, 
  tfe_core(NewSRC, TGT, NewDFP), !.

tfe_core(SRC, TGT, DFP) :-
  SRC = (_, SF),
  tfe_type(SF, b), 
  i_b(SRC, DFP, SRC_L, DFP_L, SRC_R, DFP_R), !, 
  tfe_core(SRC_L, TGT, DFP_L), !,
  tfe_core(SRC_R, TGT, DFP_R), !.

tfe_core(OSF0, OSF1, DFP) :- 
  para_step(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP), !, 
  tfe_core(NewOSF0, NewOSF1, NewDFP), !.

tfe_core(OSF0, OSF1, DFP) :- 
  (
    i_ab(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) ; 
    i_ba(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) 
  ), !,  
  tfe_core(OSF0L, OSF1L, DFP_L), !,
  tfe_core(OSF0R, OSF1R, DFP_R), !.

dff([OPF | OPFs], ONF, DFP) :- 
  sort(OPFs, Defs),
  dff(Defs, OPF, ONF, DFP).

dff(Defs, OSF0, OSF1, DFP) :- 
  para_step(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP), !, 
  dff(Defs, NewOSF0, NewOSF1, NewDFP).

dff(Defs, OSF0, OSF1, DFP) :- 
  (
    i_ab(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) ; 
    i_ba(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) 
  ), !,  
  dff(Defs, OSF0L, OSF1L, DFP_L),
  dff(Defs, OSF0R, OSF1R, DFP_R).

dff(_, OSF0, OSF1, DFP) :-
  mate(OSF0, OSF1, DFP). 

dff(Defs, OSF0, OSF1, DFP) :-
  OSF1 = (_, (+ Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  i_a(l, IFF, DFP0, IMP, DFP1), 
  i_b(IMP, DFP1, Ante, DFP2, Cons, DFP3), 
  mate(OSF1, Ante, DFP2), 
  dff(Defs, OSF0, Cons, DFP3).

dff(Defs, OSF0, OSF1, DFP) :-
  OSF1 = (_, (- Atom)), 
  uatom(Atom), 
  member(Def, Defs), 
  many_nb([c], [Def], DFP, [IFF], DFP0), 
  IFF = (_, (+ Atom <=> _)), !,
  i_a(r, IFF, DFP0, IMP, DFP1), 
  i_b(IMP, DFP1, Ante, DFP2, Cons, DFP3), 
  mate(OSF1, Cons, DFP3), 
  dff(Defs, OSF0, Ante, DFP2).

spl_once((IDL, (+ (Atom => Form))), (IDR, (+ Atom)), IPP, NewISF, NewIPP) :- 
  i_b((IDL, (+ (Atom => Form))), IPP, TempISF, TempIPP, NewISF, NewIPP),
  mate((IDR, (+ Atom)), TempISF, TempIPP).

spl_once((IDL, (+ Form => Atom)), (IDR, (- Atom)), IPP, NewISF, NewIPP) :- 
  i_b((IDL, (+ (Form => Atom))), IPP, NewISF, NewIPP, TempISF, TempIPP), 
  mate((IDR, (- Atom)), TempISF, TempIPP).

spl_many(_, [], Prf, [], Prf). 

spl_many(SignImps, [Satom | Satoms], IPP, [ISF | ISFs], NewIPP) :- 
  member(SignImp, SignImps), 
  spl_once(SignImp, Satom, IPP, ISF, TempIPP),
  spl_many(SignImps, Satoms, TempIPP, ISFs, NewIPP).

spl_aux(ISFsA, (ISFsB, IPP)) :- 
  append(ISFsA, ISFsB, ISFs),
  prop_tblx((ISFs, IPP)).

spl([IPF | SignDefs], INF, IPP) :- 
 many_nb([a], SignDefs, IPP, SignImps, IPP0), !, 
 many_nb([a, n], [INF], IPP0, ISFsA, IPP1), !,
 spl_many(SignImps, ISFsA, IPP1, Dfns, IPP2), !,
 many_nb([a, d, n], Dfns, IPP2, ISFsB, IPP3), !,
 append(ISFsA, ISFsB, ISFs), !,
 many([a, b, c, n], ([IPF], IPP3), IIPPs), !,
 maplist(osfs_odfp(ISFs), IIPPs).

ptblx(IPFs, INF, IPP) :- 
  prop_tblx(([INF | IPFs], IPP)).  

osf_mgu_osf((_, (+ FormA)), (_, (- FormB))) :- 
  form_mgu_form(FormA, FormB).

osf_mgu_osf((_, (- FormA)), (_, (+ FormB))) :- 
  form_mgu_form(FormA, FormB).

form_mgu_form(FormA, FormB) :- 
  unifiable(FormA, FormB, Unif),
  maplist(is_renaming, Unif).
  
form_mgu_form(TermA = TermB, FormB) :- 
  unifiable((TermB = TermA), FormB, Unif),
  maplist(is_renaming, Unif).

is_renaming((X = Y)) :- 
  var(X), 
  \+ var(Y),
  Y = @(Num),
  number(Num).

pivot_aux(OSFs, ([OSF1], DFP)) :- 
  member(OSF0, OSFs), 
  osf_mgu_osf(OSF0, OSF1),
  mate(OSF0, OSF1, DFP).

pivot_osa(OSA, OSFs, OSF, DFP) :- 
  many([b, c, n], ([OSF], DFP), ODFPs), 
  pluck(ODFPs, ([NewOSF], NewDFP), Rest), 
  mate(OSA, NewOSF, NewDFP), 
  maplist(pivot_aux([OSA | OSFs]), Rest).

res([OPF0, OPF1], ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, TempDFP), 
  OPF1 = (_, PF1), 
  qla_sas(PF1, SAs),
  member(SA, SAs),
  i_f_s(SA, TempDFP, ORSA, DFP0, OLSA, DFP1), 
  pivot_osa(OLSA, OSFs, OPF0, DFP1), 
  pivot_osa(ORSA, OSFs, OPF1, DFP0). 

dir_iff(l, l, l).
dir_iff(l, r, r).
dir_iff(r, l, r).
dir_iff(r, r, l).

osfs_odfp(OSFs0, (OSFs1, IPP)) :- 
  member(OSF0, OSFs0), 
  member(OSF1, OSFs1), 
  mate(OSF0, OSF1, IPP).

pivot_subsume(OSFs, OSF, DFP, NewOSF, NewDFP) :- 
  OSF = (_, SF), 
  qla_sas(SF, SAs), 
  member(SA, SAs),
  i_f_s(SA, DFP, TempOSF, TempDFP, NewOSF, NewDFP), 
  many([b, c, n], ([OSF], TempDFP), ODFPs),
  maplist(osfs_odfp([TempOSF | OSFs]), ODFPs). 

pivot_one(OSFs, OSF, DFP, NewOSF, NewDFP) :- 
  many([b, c, n], ([OSF], DFP), ODFPs),
  pluck(ODFPs, ([NewOSF], NewDFP), Rest), 
  maplist(osfs_odfp(OSFs), Rest). 

pivot(ISFs, IPF0, IPF1, IPP, ISAtom0, ISAtom1, NewIPP) :- 
  many([b, c, n], ([IPF0], IPP), IIPPs0),
  pluck(IIPPs0, ([ISAtom0], TempIPP), Rest0), 
  maplist(osfs_odfp(ISFs), Rest0), 
  many([b, c, n], ([IPF1], TempIPP), IIPPs1),
  pluck(IIPPs1, ([ISAtom1], NewIPP), Rest1), 
  maplist(osfs_odfp(ISFs), Rest1). 

fa_unit(! Form) :- 
  fa_unit(Form). 

fa_unit(Atom) :-
  uatom(Atom). 

not_fa(Form) :- 
  Form \= (! _).

ncjtr([ONF0], ONF1, DFP) :- 
  i_n(ONF1, DFP, OPF, TempDFP), 
  mate_pn(OPF, ONF0, TempDFP).

bwd([OPF0, OPF1], ONF, DFP) :- 
  sup(OPF1, OPF0, ONF, DFP).

fwd([OPF0, OPF1], ONF, DFP) :- 
  sup(OPF0, OPF1, ONF, DFP).

sup([IPF0, IPF1], INF, IPP) :- 
  sup(IPF0, IPF1, INF, IPP).

is_ose(OSF) :- 
  is_ope(OSF) ;
  is_one(OSF).

is_ope((_, (+ _ = _))).
is_one((_, (- _ = _))).

inst_fas(Form, Form) :-
  Form \= (! _).
  
inst_fas(! Form, Body) :-
  subst(_, Form, TempForm),
  inst_fas(TempForm, Body).

term_poseq_term(Var, _) :- 
  var(Var).

term_poseq_term(_, Var) :- 
  var(Var).

term_poseq_term(TermA, TermB) :- 
  \+ var(TermA),
  \+ var(TermB),
  TermA = @(Num),
  TermB = @(Num).

term_poseq_term(TermA, TermB) :- 
  \+ var(TermA),
  \+ var(TermB),
  TermA = (Fun ^ TermsA),
  TermB = (Fun ^ TermsB),
  length(TermsA, Lth),
  length(TermsB, Lth).

term_poseq_term(_, TermA, TermB) :- 
  term_poseq_term(TermA, TermB).

term_poseq_term(OPQEs, TermA, TermB) :- 
  member((_, (+ QE)), OPQEs), 
  inst_fas(QE, TermL = TermR), 
  ( 
    term_poseq_term(TermA, TermL) ; 
    term_poseq_term(TermA, TermR) ; 
    term_poseq_term(TermB, TermR) ; 
    term_poseq_term(TermB, TermL) 
  ).

sup(OPF0, OPF1, ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, DFP0), 
  pivot_one(OSFs, OPF0, DFP0, SRC, DFP1), 
  pivot_one(OSFs, OPF1, DFP1, PreOPE, DFP2), 
  is_ope(PreOPE),
  set_dir(PreOPE, DFP2, OPE, DFP3),
  member_rev(TGT, OSFs),
  subst_rel_single(SRC, OPE, TGT, DFP3). 

qla_sas(SF, SAs) :- 
  b_c(_, SF, NewSF), 
  qla_sas(NewSF, SAs).

qla_sas(SF, SAs) :- 
  b_n(SF, NewSF), 
  qla_sas(NewSF, SAs).

qla_sas(SF, SAs) :- 
  b_b(SF, SF0, SF1), 
  qla_sas(SF0, SAs0),
  qla_sas(SF1, SAs1),
  append(SAs0, SAs1, SAs).

qla_sas(SF, [SF]) :- 
  satom(SF).

pf_form(+ Form, Form).

get_pfx([(_, (+ Prem)) | _], Pfx) :- 
  (Prem = (Lit | _) ; Prem = Lit), !,
  (Lit = (~ Atom) ; Lit = Atom), !,
  atom_string(Atom, String), 
  split_string(String, "_", "", [Pfx, _]).

asr(IPFs, (_, (- $false)), IPP) :- 
  get_pfx(IPFs, Pfx),
  maplist_cut(ipf_nums, IPFs, Numss),
  numss_dimacs(Numss, DIMACS),
  write_file("temp.cnf", DIMACS), !,
  shell("cadical -q temp.cnf temp.drat", _), !,
  shell("drat-trim temp.cnf temp.drat -L temp.lrat", _), !,
  file_rups(Pfx, "temp.lrat", RUPs), 
  maplist_idx(mk_pair, 1, IPFs, SISFs), 
  add_clas_by_rups(SISFs, RUPs, IPP),
  delete_file("temp.cnf"),
  delete_file("temp.drat"),
  delete_file("temp.lrat").

acmp(OPFs, ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, TempDFP), 
  many([a, b, c, n], (OPFs, TempDFP), ODFPs), 
  maplist(osfs_odfp(OSFs), ODFPs).

der([OPF], ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, DFP0), 
  pivot_one(OSFs, OPF, DFP0, OSF0, DFP1), 
  OSF0 = (_, (+ TermA = TermB)), 
  format('First term = ~w\n', TermA), 
  format('First term = ~w\n', TermB),
  i_h((- TermA = TermB), ne_eval, DFP1, OSF1, DFP2), 
  mate_pn(OSF0, OSF1, DFP2).

opqla_onqla(OPQla, ONQla, DFP) :- 
  many_nb([a, d, n], [ONQla], DFP, OSFs, TempDFP), 
  many([b, c, n], ([OPQla], TempDFP), ODFPs), 
  maplist(osfs_odfp(OSFs), ODFPs).

opqla_onqla_cut(OPQla, ONQla, DFP) :- 
  many_nb([a, d, n], [ONQla], DFP, OSFs, TempDFP), 
  many([b, c, n], ([OPQla], TempDFP), ODFPs), 
  maplist_cut(osfs_odfp(OSFs), ODFPs).

para_step(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP) :- 
  para_step_core(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP) ; 
  para_step_core(OSF1, OSF0, DFP, NewOSF1, NewOSF0, NewDFP). 

para_step_core(OSF0, OSF1, DFP, NewOSF0, OSF1, NewDFP) :- 
  i_n(OSF0, DFP, NewOSF0, NewDFP). 
  
para_step_core(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP) :- 
  i_cd(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP).

para(ISF0, ISF1, IPP) :- 
  mate(ISF0, ISF1, IPP).

para(ISF0, ISF1, IPP) :- 
  para_core(ISF0, ISF1, IPP).

para(ISF0, ISF1, IPP) :- 
  para_core(ISF1, ISF0, IPP).

para_core(ISF0, ISF1, IPP) :- 
  i_n(ISF0, IPP, NewISF0, NewIPP), !,
  para(NewISF0, ISF1, NewIPP).

para_core(ISF0, ISF1, IPP) :- 
  i_b(ISF1, IPP, ISF1A, IPP_A, ISF1B, IPP_B), 
  (
    (
      i_a(l, ISF0, IPP_A, ISF0L, IPP_L), 
      i_a(r, ISF0, IPP_B, ISF0R, IPP_R), 
      para(ISF0L, ISF1A, IPP_L),
      para(ISF0R, ISF1B, IPP_R)
    ) ;
    (
      i_a(l, ISF0, IPP_B, ISF0L, IPP_L), 
      i_a(r, ISF0, IPP_A, ISF0R, IPP_R), 
      para(ISF0L, ISF1B, IPP_L),
      para(ISF0R, ISF1A, IPP_R)
    ) 
  ).

para_core(ISF0, ISF1, DFP) :- 
  DFP = (_, FP, _), 
  i_d(ISF1, DFP, NewISF1, TempIPP),
  i_c(@(FP), ISF0, TempIPP, NewISF0, NewIPP),
  para(NewISF0, NewISF1, NewIPP).

osf_equiv_osf((_, SF_A), (_, SF_B)) :- 
  sf_equiv_sf(SF_A, SF_B).

sf_equiv_sf(+ FormA, + FormB) :- 
  form_equiv_form(FormA, FormB).

sf_equiv_sf(- FormA, - FormB) :- 
  form_equiv_form(FormA, FormB).

osfs_match_osf(OSFs, OSF) :- 
  member(Mch, OSFs), 
  osf_matches_osf(Mch, OSF).

osf_matches_osf((_, SF_A), (_, SF_B)) :- 
  sf_matches_sf(SF_A, SF_B).

sf_matches_sf(+ FormA, - FormB) :- 
  form_equiv_form(FormA, FormB).

sf_matches_sf(- FormA, + FormB) :- 
  form_equiv_form(FormA, FormB).

v_cnf([IPF], INF, IPP) :- 
  many_nb([a, d, n], [INF], IPP, ISFs, NewIPP),
  cnf_aux(ISFs, IPF, NewIPP).

cnf_aux(ISFs, ISF, IPP) :- 
  (
    i_a(l, ISF, IPP, NewISF, NewIPP),
    cnf_aux(ISFs, NewISF, NewIPP) 
  ) ; 
  (
    i_a(r, ISF, IPP, NewISF, NewIPP),
    cnf_aux(ISFs, NewISF, NewIPP) 
  ).

cnf_aux(ISFs, ISF, IPP) :- 
  i_c(_, ISF, IPP, NewISF, NewIPP), !,
  cnf_aux(ISFs, NewISF, NewIPP). 

cnf_aux(OSFs, OSF, DFP) :- 
  i_n(OSF, DFP, NewOSF, NewDFP), 
  cnf_aux(OSFs, NewOSF, NewDFP).

cnf_aux(OSFs, OSF, DFP) :- 
  i_b(OSF, DFP, OSF_L, DFP_L, OSF_R, DFP_R), 
  cnf_aux(OSFs, OSF_L, DFP_L),
  cnf_aux(OSFs, OSF_R, DFP_R).

cnf_aux(OSFs, OSF, DFP) :- 
  \+ type_osf(a, OSF),
  \+ type_osf(b, OSF),
  \+ type_osf(c, OSF),
  \+ type_osf(n, OSF),
  member(Match, OSFs),
  mate(OSF, Match, DFP).

is_opf((_, (+ _))).
is_onf((_, (- _))).

skm_aux(AOCs, OSF0, OSF1, DFP) :- 
  (
    i_ab(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) ;
    i_ba(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R)
  ), 
  skm_aux(AOCs, OSF0L, OSF1L, DFP_L),
  skm_aux(AOCs, OSF0R, OSF1R, DFP_R).

skm_aux(AOCs, OSF0, OSF1, DFP) :- 
  (
    i_cd(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP) ;
    i_cd(OSF1, OSF0, DFP, NewOSF1, NewOSF0, NewDFP)
  ), 
  skm_aux(AOCs, NewOSF0, NewOSF1, NewDFP).

skm_aux(_, ISF0, ISF1, IPP) :-  
  mate(ISF0, ISF1, IPP).

skm_aux(AOCs, OPF, ONF, DFP) :- 
  is_opf(OPF),
  is_onf(ONF),
  pluck(AOCs, AOC, Rest),
  many_nb([c], [AOC], DFP, [TempOSF], TempDFP), 
  TempOSF = (_, (+ _ => _)),
  i_b(TempOSF, TempDFP, OSF_L, DFP_L, OSF_R, DFP_R), 
  i_x(OPF, OSF_L, DFP_L),
  skm_aux(Rest, OSF_R, ONF, DFP_R).

% skm_core(PosAOCs, HypA, HypB, Goal) :-  
%   skm_aux(PosAOCs, HypA, HypB, Goal) ;  
%   skm_aux(PosAOCs, HypB, HypA, Goal).

skm([OPF | AOCs], ONF, IPP) :-  
  skm_aux(AOCs, OPF, ONF, IPP).

ppr([OPF], ONF, DFP) :- 
  ppr_core(OPF, ONF, DFP).

ppr_core(OSF0, OSF1, DFP) :- 
  para_step(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP), !, 
  ppr_core(NewOSF0, NewOSF1, NewDFP).

ppr_core(OSF0, OSF1, DFP) :- 
  (
    i_ab(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) ; 
    i_ba(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R) 
  ),
  ppr_core(OSF0L, OSF1L, DFP_L),
  ppr_core(OSF0R, OSF1R, DFP_R).

ppr_core(OSF0, OSF1, DFP) :- 
  (i_a(l, OSF0, DFP, NewOSF0, NewDFP), ppr_core(NewOSF0, OSF1, NewDFP)) ;
  (i_a(r, OSF0, DFP, NewOSF0, NewDFP), ppr_core(NewOSF0, OSF1, NewDFP)).
  
ppr_core(OSF0, OSF1, DFP) :- 
  mate(OSF0, OSF1, DFP).

dfu([OPF | OPFs], ONF, DFP) :- 
  dfu(OPFs, OPF, ONF, DFP).

dfu(Defs, OSF0, OSF1, DFP) :- 
  many_nb([a, d, n], [OSF1], DFP, OSFs, TempDFP),
  many([b, c, n], ([OSF0], TempDFP), ODFPs),
  member(Dir, [l, r]),
  dfu_odfps(Dir, Defs, OSFs, ODFPs).

dfu_odfps(_, [], [], []).

dfu_odfps(Dir, Defs, OSFs, [ODFP | ODFPs]) :- 
  dfu_odfp(Dir, Defs, OSFs, ODFP, NewDefs, NewOSFs),  
  dfu_odfps(Dir, NewDefs, NewOSFs, ODFPs).

dfu_odfp(Dir, OPQEs, OSFs, ([OSF0], DFP), NewOPQEs, NewOSFs) :-  
  pluck(OSFs, OSF1, NewOSFs),
  subst_rel_multi(Dir, OSF0, OPQEs, OSF1, DFP, NewOPQEs).


timed_call(Time, Goal, AltGoal) :- 
  catch(
    call_with_time_limit(
      Time, 
      call(Goal) -> 
      true ;
      throw(time_limit_exceeded)
    ),
    time_limit_exceeded, 
    call(AltGoal)
  ). 

timed_call(TIME, GOAL) :- 
  timed_call(TIME, GOAL, false). 

elabs(_, [], _, Goal) :- 
  Goal = ([+ $false | _], _, _), 
  g_h(- $false, neg_false, Goal, NewGoal), 
  g_x(1, 0, NewGoal).

elabs(PROC, [Hint | Hints], FIDs, Goal) :- 
  timed_call(
    10, 
    call(PROC, Hint, FIDs, Goal, NewFIDs, NewGoal), 
    (
      report_elab_fail(Hint, FIDs, Goal), 
      % throw(elaboration_failed)
      false
    )
  ), !, 
  elabs(PROC, Hints, NewFIDs, NewGoal).

add_aocs([], [], FIDs, Goal, FIDs, Goal).

add_aocs([AOC | AOCs], [Skm | Skms], FIDs, Goal, NewFIDs, NewGoal) :- 
  g_h(+ AOC, aoc(Skm), Goal, TempGoal), 
  add_aocs(AOCs, Skms, [none | FIDs], TempGoal, NewFIDs, NewGoal).

app_aocs(OSF, [AOC | AOCs], DFP, NewOSF, NewDFP) :-  
  many_nb([c], [AOC], DFP, [OPImp], DFP0), 
  i_b(OPImp, DFP0, OSF_L, DFP_L, OSF_R, DFP_R), 
  osf_matches_osf(OSF, OSF_L),
  mate(OSF, OSF_L, DFP_L), 
  app_aocs(OSF_R, AOCs, DFP_R, NewOSF, NewDFP).

app_aocs(PrevCons, [], Goal, PrevCons, Goal). 

aocs_opfs([], []).

aocs_opfs([AOC | AOCs], [(OS, (+ AOC)) | OPFs]) :- 
  aocs_opfs(AOCs, OPFs),
  length(OPFs, Lth), 
  OS is Lth + 1.

aoc(OPFs, ONF, DFP) :- 
  many_nb([d], [ONF], DFP, [TempONF], DFP0), 
  TempONF = (_, (- (_ => _))),
  i_aa(TempONF, DFP0, OPAnte, ONCons, DFP1), 
  app_aocs(OPAnte, OPFs, DFP1, NewOPF, DFP2), 
  para(NewOPF, ONCons, DFP2).

get_prob(_, [], []).

get_prob(NUM, [SF | CTX], [(NUM, SF) | PROB]) :-
  SUCC is NUM + 1, 
  get_prob(SUCC, CTX, PROB). 

get_prob(Num, [], CTX, PROB) :- 
  get_prob(Num, CTX, PROB).

get_prob(NUM, [_ | FIDS], [_ | CTX], PROB) :- 
  SUCC is NUM + 1, 
  get_prob(SUCC, FIDS, CTX, PROB).

pos_osf((_, (+ _))).
neg_osf((_, (- _))).

print_ctx_size([], _). 

print_ctx_size([(ID, _, _, _) | Hints], Ctx) :- 
  length([ID | Ctx], Num),
  format('~w\n', Num), 
  print_ctx_size(Hints, [ID | Ctx]).

print_ctx_size([del(ID) | Hints], Ctx) :- 
  remove_once(Ctx, ID, NewCtx),
  length(NewCtx, Num),
  format('~w\n', Num), 
  print_ctx_size(Hints, NewCtx).
  
pick_pmt_both(OSFS, OSF, DFP) :- 
  member(CMP, OSFS), 
  (
    pmt(CMP, OSF, DFP) ;
    (
      many_nb([d], [OSF], DFP, [NEW_OSF], TEMP_DFP),
      many_nb([c], [CMP], TEMP_DFP, [NEW_CMP], NEW_DFP),
      pmt(NEW_CMP, NEW_OSF, NEW_DFP) 
    )
  ).

pick_pmt(OSFS, OSF, DFP) :- 
  member(CMP, OSFS), 
  pmt(CMP, OSF, DFP).

mk_hyp(_, [], []). 

bg_fresh_pars(Hyp, Num, NewHyp) :- 
  fresh_par(Hyp, Par),
  (
    b_c(@(Par), Hyp, TempHyp) -> 
    (
      bg_fresh_pars(TempHyp, Pred, NewHyp),
      Num is Pred + 1
    ) ; 
    (
      Num = 0, 
      NewHyp = Hyp
    )
  ).

tir([OPF], _, DFP) :- 
  OPF = (_, (+ ~ (Term = Term))),
  i_n(OPF, DFP, ONF, NewDFP),
  eq_refl(ONF, NewDFP).

tir([OPF], ONF, DFP) :- 
  OPF = (_, (+ (~ (Term = Term) | Form))),
  ONF = (_, (- Form)),
  i_b(OPF, DFP, OSF_L, DFP_L, OSF_R, DFP_R), 
  i_n(OSF_L, DFP_L, NewOSF_L, NewDFP_L), 
  eq_refl(NewOSF_L, NewDFP_L),
  mate(OSF_R, ONF, DFP_R).

tir([OPF], ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, DFP0), 
  many([b, c, n], ([OPF], DFP0), ODFPs), !,
  maplist(tir_aux(OSFs), ODFPs).

tir_aux(_, ([ONF], DFP)) :- 
  ONF = (_, (- TermA = TermB)),
  unify_with_occurs_check(TermA, TermB),
  eq_refl(ONF, DFP).

tir_aux(OSFs, ODFP) :- 
  osfs_odfp(OSFs, ODFP).

wkn([OPF], ONF, DFP) :- 
  opqla_onqla(OPF, ONF, DFP).

updr([OPF], ONF, DFP) :- 
  many_nb([d], [ONF], DFP, [NewONF], DFP0),
  many_nb([c], [OPF], DFP0, [NewOPF], DFP1),
  prop_tblx(([NewOPF, NewONF], DFP1)).

eqf_aux(OSFs, OPEq, ([OSF1], DFP)) :- 
  member(OSF0, OSFs), 
  subst_rel_single(OSF0, [OPEq], OSF1, DFP).

eqf([OPF], ONF, DFP) :-
  many_nb([a, d, n], [ONF], DFP, OSFs, TempDFP), 
  pluck(OSFs, OPEq, Rest), 
  OPEq = (_, (+ _ = _)), 
  many([b, c, n], ([OPF], TempDFP), ODFPs), 
  maplist(eqf_aux(Rest, OPEq), ODFPs).

eqr([OPF], ONF, DFP) :- 
  many_nb([a, d, n], [ONF], DFP, OSFs, DFP0), 
  many([b, c, n], ([OPF], DFP0), ODFPs), !,
  pluck(ODFPs, ([OSF], DFP1), Rest), 
  OSF = (_, (- (TermA = TermB))), 
  unify_with_occurs_check(TermA, TermB),
  eq_refl(OSF, DFP1),
  maplist(osfs_odfp(OSFs), Rest).

goal_dfp((_, FP, Prf), (0, FP, Prf)).

play_prf(a(Dir, Pos, Prf), Goal) :- 
  g_a(Dir, Pos, Goal, NewGoal), 
  play_prf(Prf, NewGoal).

play_prf(b(Idx, PrfL, PrfR), Goal) :- 
  g_b(Idx, Goal, GoalL, GoalR), 
  play_prf(PrfL, GoalL),
  play_prf(PrfR, GoalR).

play_prf(c(Term, ID, Prf), Goal) :- 
  g_c(Term, ID, Goal, NewGoal), 
  play_prf(Prf, NewGoal).

play_prf(d(Idx, Prf), Goal) :- 
  g_d(Idx, Goal, NewGoal), 
  play_prf(Prf, NewGoal).

play_prf(f(Conc, PrfA, PrfB), Goal) :- 
  g_f(Conc, Goal, GoalA, GoalB), 
  play_prf(PrfA, GoalA), 
  play_prf(PrfB, GoalB). 

play_prf(h(SF, Jst, Prf), Goal) :- 
  g_h(SF, Jst, Goal, NewGoal), 
  play_prf(Prf, NewGoal). 

play_prf(n(Idx, Prf), Goal) :- 
  g_n(Idx, Goal, NewGoal), 
  play_prf(Prf, NewGoal).

play_prf(x(Pdx, Ndx), Goal) :- 
  g_x(Pdx, Ndx, Goal).

get_aocs(Form, Skms, AOCs) :- 
  strip_fas(Form, Num, Ante => Cons), 
  mk_vars(Num, RevVars),
  reverse(RevVars, Vars), 
  get_aocs_aux(Vars, Ante, Cons, Skms, Forms),
  maplist_cut(mk_fa(Num), Forms, AOCs).

rtf([IPF], INF, IPP) :- 
  rtf_aux(IPF, INF, IPP).

rtf_aux(IPF, INF, IPP) :-
  rtf_core(IPF, INF, IPP) ;
  rtf_core(INF, IPF, IPP).

rtf_core(OSF0, OSF1, DFP) :- 
  i_n(OSF0, DFP, NEW_OSF0, NEW_DFP), !,
  rtf_aux(NEW_OSF0, OSF1, NEW_DFP).

rtf_core(IPF, INF, IPP) :- 
  many_nb([d], [INF], IPP, [ISF0], TempIPP), 
  many_nb([c], [IPF], TempIPP, [ISF1], NewIPP), 
  para(ISF0, ISF1, NewIPP).

ennf([IPF], INF, IPP) :- 
  para(IPF, INF, IPP).

mk_fa(Form, ! Form).

mk_fa(0, Form, Form).

mk_fa(Num, Form, ! NewForm) :- 
  num_pred(Num, Pred), 
  mk_fa(Pred, Form, NewForm).

get_aocs_aux(_, Ante, Cons, [], []) :- 
  para((0, (+ Ante)), (1, (- Cons)), (0, 0, _)).

get_aocs_aux(Vars, ? Ante, Cons, [Skm | Skms], [(? Ante) => NewAnte | AOCs]) :- 
  subst((Skm ^ Vars), Ante, NewAnte), 
  get_aocs_aux(Vars, NewAnte, Cons, Skms, AOCs).

mk_pair(X, Y, (X, Y)).

nums_dimacs(Nums, Str) :- 
  maplist(number_string, Nums, Strs),
  strings_concat_with(" ", Strs, TempStr),
  string_concat(TempStr, " 0", Str).

nums_maxvar(Nums, MaxVar) :-
  maplist_cut(abs, Nums, Nats),
  max_list(Nats, MaxVar).

numss_maxvar(Numss, MaxVar) :-
  maplist(nums_maxvar, Numss, MaxVars),
  max_list(MaxVars, MaxVar).

numss_dimacs(Numss, DIMACS) :-
  numss_maxvar(Numss, MaxVar), 
  number_string(MaxVar, MaxVarStr),
  length(Numss, NumCla),
  number_string(NumCla, NumClaStr),
  strings_concat(["p cnf ", MaxVarStr, " ", NumClaStr], Str),
  maplist(nums_dimacs, Numss, Strs),
  strings_concat_with("\n", [Str | Strs], DIMACS).

aoc_norm(! Form, Num, Skm, ! Norm) :-
  Succ is Num + 1, 
  aoc_norm(Form, Succ, Skm, Norm).
  
aoc_norm((? Ante) => _, Num, Skm, (? Ante) => Cons) :-
  mk_skm_term(Skm, Num, SkmTerm), 
  subst(SkmTerm, Ante, Cons).

pmt_a_aux(OSF, DFP, OSF_L, OSF_R, NEW_DFP) :- 
  \+ imp_osf(OSF), 
  i_a(l, OSF, DFP, OSF_L, TEMP_DFP),
  i_a(r, OSF, TEMP_DFP, OSF_R, NEW_DFP).

pmt_a(OSF, DFP, OSFS, NEW_DFP) :- 
  pmt_a_aux(OSF, DFP, OSF_L, OSF_R, DFP0) -> 
  (
    pmt_a(OSF_L, DFP0, OSFS_L, DFP1),
    pmt_a(OSF_R, DFP1, OSFS_R, NEW_DFP), 
    append(OSFS_L, OSFS_R, OSFS)
  ) ;
  (OSFS = [OSF], NEW_DFP = DFP).

pmt_b(OSF, DFP, ODFPS) :- 
  (
    \+ imp_osf(OSF),
    i_b(OSF, DFP, OSF_L, DFP_L, OSF_R, DFP_R)
  ) -> 
  (
    pmt_b(OSF_L, DFP_L, ODFPS_L),
    pmt_b(OSF_R, DFP_R, ODFPS_R),
    append(ODFPS_L, ODFPS_R, ODFPS)
  ) ;
  ODFPS = [([OSF], DFP)].

pmt_l([], []).

pmt_l(OSFS, [([OSF1], DFP) | ODFPS]) :- 
  pluck(OSFS, OSF0, REST), 
  pmt(OSF0, OSF1, DFP), 
  pmt_l(REST, ODFPS).

pmt_r([], []).

pmt_r(OSFS, [([OSF1], DFP) | ODFPS]) :- 
  pluck(OSFS, OSF0, REST), 
  pmt(OSF1, OSF0, DFP), 
  pmt_r(REST, ODFPS).

pmt(OSF0, OSF1, DFP) :- 
  mate(OSF0, OSF1, DFP).

pmt(OSF0, OSF1, DFP) :- 
  para_step(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP), !, 
  pmt(NewOSF0, NewOSF1, NewDFP).

pmt(OSF_A, OSF_B, DFP) :- 
  imp_osf(OSF_A),
  i_ab(OSF_A, OSF_B, DFP, OSF_AL, OSF_BL, DFP_L, OSF_AR, OSF_BR, DFP_R), !,
  pmt(OSF_AL, OSF_BL, DFP_L), !, 
  pmt(OSF_AR, OSF_BR, DFP_R), !. 

pmt(OSF_A, OSF_B, DFP) :- 
  imp_osf(OSF_B),
  i_ba(OSF_A, OSF_B, DFP, OSF_AL, OSF_BL, DFP_L, OSF_AR, OSF_BR, DFP_R), !,
  pmt(OSF_AL, OSF_BL, DFP_L), !,
  pmt(OSF_AR, OSF_BR, DFP_R), !. 

pmt(OSF0, OSF1, DFP) :- 
  \+ imp_osf(OSF0),
  type_osf(a, OSF0),
  pmt_a(OSF0, DFP, OSFs, TempDFP), !,  
  pmt_b(OSF1, TempDFP, ODFPs), 
  pmt_l(OSFs, ODFPs).

pmt(OSF0, OSF1, DFP) :- 
  \+ imp_osf(OSF1),
  type_osf(a, OSF1),
  pmt_a(OSF1, DFP, OSFs, TempDFP), !,  
  pmt_b(OSF0, TempDFP, ODFPs), 
  pmt_r(OSFs, ODFPs).

imp_osf(OSF) :- 
  OSF = (_, SF),
  sf_form(SF, FORM),
  member(FORM, [(_ => _), (_ <=> _)]).

sf_form(+ Form, Form).
sf_form(- Form, Form).

flt_fgs([], []).

flt_fgs([OSF0 | OSFs0], [([OSF1], DFP) | ODFPs]) :- 
  flt_core(OSF0, OSF1, DFP), !,
  flt_fgs(OSFs0, ODFPs).

flt_a(OSF, DFP, [OSF], DFP) :- 
  \+ type_osf(a, OSF).

flt_a(OSF, DFP, OSFs, NewDFP) :- 
  type_osf(a, OSF),
  i_aa(OSF, DFP, OSF_L, OSF_R, DFP0), 
  flt_a(OSF_L, DFP0, OSFsL, DFP1), 
  flt_a(OSF_R, DFP1, OSFsR, NewDFP), 
  append(OSFsL, OSFsR, OSFs).

flt_core(HypA, HypB, Goal) :- 
  flt_dir(HypA, HypB, Goal) ;
  flt_dir(HypB, HypA, Goal).

flt_dir(ISF0, ISF1, DFP) :-
  mate_pn(ISF0, ISF1, DFP). 

flt_dir(OSF0, OSF1, DFP) :- 
  type_osf(a, OSF0),
  flt_a(OSF0, DFP, OSFs, TempDFP), !,
  many([b], ([OSF1], TempDFP), ODFPs), 
  flt_fgs(OSFs, ODFPs).

flt_dir(OSF0, OSF1, DFP) :- 
  type_osf(c, OSF0), 
  i_cd(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP), !, 
  flt_core(NewOSF0, NewOSF1, NewDFP).

flt_dir(OSF0, OSF1, DFP) :- 
  type_osf(n, OSF0), 
  i_n(OSF0, DFP, NewOSF0, NewDFP), !,
  flt_core(NewOSF0, OSF1, NewDFP). 

flt([OPF], ONF, DFP) :- 
  flt_core(OPF, ONF, DFP).

nnf([OPF], ONF, DFP) :- 
  nnf_core(OPF, ONF, DFP).

nnf_core(OSF0, OSF1, DFP) :- 
  i_n(OSF0, DFP, NewOSF0, NewDFP), !,  
  nnf_core(NewOSF0, OSF1, NewDFP).

nnf_core(OSF0, OSF1, DFP) :- 
  i_n(OSF1, DFP, NewOSF1, NewDFP), !,  
  nnf_core(OSF0, NewOSF1, NewDFP).

nnf_core(OSF0, OSF1, DFP) :- 
  (
    i_cd(OSF0, OSF1, DFP, NewOSF0, NewOSF1, NewDFP) ; 
    i_cd(OSF1, OSF0, DFP, NewOSF1, NewOSF0, NewDFP) 
  ), !, 
  nnf_core(NewOSF0, NewOSF1, NewDFP).

nnf_core(OSF0, OSF1, DFP) :- 
  i_ab_sw(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R), 
  nnf_core(OSF0L, OSF1L, DFP_L),
  nnf_core(OSF0R, OSF1R, DFP_R).

nnf_core(OSF0, OSF1, DFP) :- 
  OSF0 \= (_, (- (_ <=> _))),
  i_ba_sw(OSF0, OSF1, DFP, OSF0L, OSF1L, DFP_L, OSF0R, OSF1R, DFP_R), 
  nnf_core(OSF0L, OSF1L, DFP_L),
  nnf_core(OSF0R, OSF1R, DFP_R).

nnf_core(OSF0, OSF1, DFP) :- 
  OSF0 = (_, (- (FormL <=> FormR))),
  i_f(((FormL | FormR) & (~ FormL | ~ FormR)), DFP, ONF, DFP_L, OPF, DFP_R),
  prop_tblx(([OSF0, ONF], DFP_L)), 
  nnf_core(OPF, OSF1, DFP_R).

nnf_core(OSF0, OSF1, DFP) :- 
  OSF0 = (_, (+ (FormL <=> FormR))),
  i_f(((FormL | FormR) & (~ FormL | ~ FormR)), DFP, ONF, DFP_L, OPF, DFP_R),
  prop_tblx(([OSF0, OPF], DFP_R)), 
  nnf_core(ONF, OSF1, DFP_L).

nnf_core(OSF0, OSF1, DFP) :- 
  i_a(l, OSF0, DFP, NewOSF0, NewDFP), 
  nnf_core(NewOSF0, OSF1, NewDFP). 

nnf_core(OSF0, OSF1, DFP) :- 
  i_a(r, OSF0, DFP, NewOSF0, NewDFP), 
  nnf_core(NewOSF0, OSF1, NewDFP). 

nnf_core(OSF0, OSF1, DFP) :-
  mate(OSF0, OSF1, DFP). 

has_eq(Exp) :-
  Exp =.. ['=' | _].

has_eq(Exp) :-
  Exp =.. [_ | Args],
  any(has_eq, Args).

scla_satoms(SC, SAs) :- 
  b_b(SC, SC_L, SC_R), 
  scla_satoms(SC_L, SAsL), 
  scla_satoms(SC_R, SAsR), 
  append(SAsL, SAsR, SAs).

scla_satoms(SC, SAs) :- 
  b_n(SC, NewSC), 
  scla_satoms(NewSC, SAs).

scla_satoms(SA, [SA]) :- 
  \+ type_sf(b, SA), 
  \+ type_sf(n, SA). 

find_new_unit_aux(SAs, SA) :- 
  member(Match, SAs), 
  sf_matches_sf(Match, SA).

find_new_unit(CtxSAs, ClaSAs, SA) :- 
  member(SA, ClaSAs), 
  delete(ClaSAs, SA, Rest),
  maplist_cut(find_new_unit_aux(CtxSAs), Rest).

add_unit_by_up(SATCTX, OSAs, SID, DFP, NewOSA, NewDFP) :-  
  maplist_cut(snd, OSAs, SAs0),
  member((SID, OSF), SATCTX), 
  snd(OSF, (+ Cla)), 
  scla_satoms(+ Cla, SAs1), 
  find_new_unit(SAs0, SAs1, NewSA), 
  (
    (
      NewSA = (+ Atom), 
      i_f(Atom, DFP, TempOSA, TempDFP, NewOSA, NewDFP)
    ) ;
    (
      NewSA = (- Atom), 
      i_f(Atom, DFP, NewOSA, NewDFP, TempOSA, TempDFP)
    )
  ), 
  many([b, n], ([OSF], TempDFP), ODFPs), 
  maplist_cut(osfs_odfp([TempOSA | OSAs]), ODFPs). 

add_units_by_ups(_, [ISA0 | ISAs], [], IPP) :- 
  member(ISA1, ISAs),
  mate(ISA0, ISA1, IPP).

add_units_by_ups(SClas, ISAtoms, [SID | SIDs], IPP) :- 
  add_unit_by_up(SClas, ISAtoms, SID, IPP, ISAtom, NewIPP), !, 
  add_units_by_ups(SClas, [ISAtom | ISAtoms], SIDs, NewIPP).

add_cla_by_rup(SISFs, rup(SID, Cla, SIDs), IPP, (SID, IPF), NewIPP) :- 
  i_f(Cla, IPP, INF, TempIPP0, IPF, NewIPP), 
  many_nb([a, n], [INF], TempIPP0, ISAtoms, TempIPP1), 
  add_units_by_ups(SISFs, ISAtoms, SIDs, TempIPP1).

add_clas_by_rups([(_, (ID, (+ $false))) | _], [], DFP) :-
  mate((ID, (+ $false)), _, DFP).

add_clas_by_rups(OClas, [Rup | Rups], DFP) :- 
  add_cla_by_rup(OClas, Rup, DFP, OCla, NewDFP),  
  add_clas_by_rups([OCla | OClas], Rups, NewDFP).

lit_atom(Lit, Atom) :- 
  Lit = (~ Atom).

lit_atom(Atom, Atom) :- 
  Atom \= (~ _).

cla_atoms(Lit | Cla, Atoms) :- 
  lit_atom(Lit, Atom),
  cla_atoms(Cla, Temp),
  ord_add_element(Temp, Atom, Atoms).

cla_atoms(Lit, [Atom]) :- 
  Lit \= (_ | _),
  lit_atom(Lit, Atom).

cla_lits(Lit | Cla, [Lit | List]) :- 
  cla_lits(Cla, List).

cla_lits(Lit, [Lit]) :- 
  Lit \= (_ | _).

lits_cla([], $false).

lits_cla(Lits, Cla) :- 
  lits_cla_core(Lits, Cla).

lits_cla_core([Lit], Lit).

lits_cla_core([Lit | Lits], Lit | Cla) :- 
  lits_cla_core(Lits, Cla).

lit_num(~ Atom, Num) :- 
  atom_num(Atom, Temp), 
  Num is (- Temp).

lit_num(Atom, Num) :- 
  Atom \= (~ _), 
  atom_num(Atom, Num).

num_lit(Pfx, Num, Atom) :- 
  0 < Num, 
  num_atom(Pfx, Num, Atom).

num_lit(Pfx, Num, ~ Atom) :- 
  Num < 0, 
  Neg is (- Num),
  num_atom(Pfx, Neg, Atom).

atom_num(Atom, Num) :- 
  atom_string(Atom, AtomStr), 
  split_string(AtomStr, "_", "", [_, NumStr]), 
  number_string(Num, NumStr).

num_atom(Pfx, Num, Atom) :- 
  number_string(Num, NumStr),
  atomics_to_string([Pfx, "_", NumStr], AtomStr),
  atom_string(Atom, AtomStr). 

ipf_nums((_, (+ Cla)), Nums) :- 
  cla_lits(Cla, Lits), 
  maplist_cut(lit_num, Lits, Nums).

nums_cla(Pfx, Nums, Cla) :- 
  maplist_cut(num_lit(Pfx), Nums, Lits),
  lits_cla(Lits, Cla). 

tstp_hints(INTP, PREC, TSTP, HINTS) :- 
  dynamic(fof/4),
  retractall(fof(_, _, _, _)),
  trim_consult(TSTP),
  findall((ID, IDs, TF, Rul), fof(ID, IDs, TF, Rul), TUPLES),
  maplist_cut(INTP, TUPLES, UNSORTED), 
  predsort(PREC, UNSORTED, HINTS).

  % findall((ID, IDs, Form, Rul), hint(ID, IDs, Form, Rul), TUPLES),
  % maplist_cut(mk_hint, TUPLES, UNSORTED), 
  % predsort(prec, UNSORTED, HINTS).

report_elab_fail((ID, Prems, Conc, Rul), FIDs, (Ctx, _)) :- 
  format('Failed step ID : ~w\n\n', ID),
  write("  ┌───────────────────────────────────────────────────────────────── Failed Goal\n"), 
  write("  │\n"),
  format('add(\n  (\n    ~w,\n    ~w,\n    ~w,\n    ~w\n  ),\n  ~w\n  (\n    ~w,\n    Prf\n  ),\n  NewGoal\n)\n\n', [ID, Prems, Conc, Rul, FIDs, Ctx]),
  open("trace.pl", write, Stream), 
  write(Stream, ":- [main].\n\n"), 
  format(Stream, '~w.\n\n', debug_id(ID)), 
  format(Stream, '~w.\n\n', debug_prems(Prems)), 
  format(Stream, '~w.\n\n', debug_conc(Conc)), 
  format(Stream, '~w.\n\n', debug_rul(Rul)), 
  format(Stream, '~w.\n\n', debug_fids(FIDs)), 
  format(Stream, '~w.\n\n', debug_ctx(Ctx)),
  close(Stream). 

conv_conc(add(ID, IDs, TPTP, Rul), add(ID, IDs, Form, Rul)) :-
  fof_form([], TPTP, Form).

conv_conc(del(ID), del(ID)).

% a : alpha
% b : beta
% c : gamma
% d : delta
% k : kappa (cut)
% n : nu (negation-decomposition)
% t : theta (theory)
% x : xi (ex falso)

prop_tblx((ISFs, IPP)) :- 
  i_h(+ $true, pos_true, IPP, IPTrue, IPP0),
  i_h(- $false, neg_false, IPP0, INFalse, IPP1),
  pluck(ISFs, ISF, Rest),
  prop_tblx(block, [], ISF, [IPTrue, INFalse | Rest], IPP1), !.

prop_tblx(Mode, Pth, ISF, ISFs, IPP) :- 
  i_n(ISF, IPP, NewISF, NewIPP), !,
  prop_tblx(Mode, Pth, NewISF, ISFs, NewIPP).

prop_tblx(Mode, Pth, ISF, ISFs, IPP) :- 
  i_aa(ISF, IPP, ISF_L, ISF_R, NewIPP), !,
  ( prop_tblx(Mode, Pth, ISF_L, [ISF_R | ISFs], NewIPP) ; 
    prop_tblx(Mode, Pth, ISF_R, [ISF_L | ISFs], NewIPP) ).

prop_tblx(block, Pth, ISF, ISFs, IPP) :- 
  i_b(ISF, IPP, ISF_L, IPP_L, ISF_R, IPP_R), !,
  prop_tblx(block, Pth, ISF_L, ISFs, IPP_L), 
  prop_tblx(block, Pth, ISF_R, ISFs, IPP_R).

prop_tblx(match, Pth, ISF, ISFs, IPP) :- 
  i_b(ISF, IPP, ISF_L, IPP_L, ISF_R, IPP_R), !,
  (
    ( prop_tblx(match, Pth, ISF_L, ISFs, IPP_L), 
      prop_tblx(block, Pth, ISF_R, ISFs, IPP_R) ) ;  
    ( prop_tblx(match, Pth, ISF_R, ISFs, IPP_R), 
      prop_tblx(block, Pth, ISF_L, ISFs, IPP_L) ) 
  ).

% If in match-mode, the signed atom in focus must match with the last signed atom added
prop_tblx(match, [ISF_L | _], ISF_R, _, IPP) :- 
  osf_matches_osf(ISF_L, ISF_R),
  mate(ISF_L, ISF_R, IPP).

% If in block-mode, the signed atom in focus can match with any signed atom on path
prop_tblx(block, Pth, OSA_R, _, DFP) :- 
  member(OSA_L, Pth),
  osf_matches_osf(OSA_L, OSA_R),
  mate(OSA_L, OSA_R, DFP).

% If in block-mode, the signed atom in focus can be pushed onto the path,
% provided it is not redundant (i.e., its equivalent is not already on the path)
prop_tblx(block, Pth, ISF, ISFs, IPP) :- 
  \+ type_osf(a, ISF),
  \+ type_osf(b, ISF),
  \+ type_osf(n, ISF),
  \+ has_equiv(ISF, Pth), % Regularity check
  pluck(ISFs, NewISF, Rest),
  prop_tblx(match, [ISF | Pth], NewISF, Rest, IPP).

has_equiv(ISF0, ISFs) :- 
  member(ISF1, ISFs),
  osf_equiv_osf(ISF0, ISF1).

form_equiv_form(FormA, FormB) :- 
  unify_with_occurs_check(FormA, FormB).
  
form_equiv_form(TermA = TermB, Form) :- 
  unify_with_occurs_check(TermB = TermA, Form).

call_with_catch(Goal, Catch) :-
  call(Goal) ->
  true ;
  (call(Catch), false).

line_step_aux(ID, Strs, add(ID, Cla, IDs)) :- 
  Strs \= ["d" | _],
  maplist(string_number, Strs, Nums), 
  append(Cla, [0 | IDs], Nums).
  
codes_numbers(Codes, Nums) :- 
  string_codes(Str, Codes), 
  split_string(Str, " ", "", Strs), 
  maplist_cut(string_number, Strs, Nums).

line_rup(Pfx, Line, rup(ID, Cla, IDs)) :- 
  codes_numbers(Line, [ID | Nums]),
  append(ClaNums, [0 | Rest], Nums), 
  nums_cla(Pfx, ClaNums, Cla),
  append(IDs, [0], Rest). 
  
file_rups(Pfx, File, RUPs) :-
  read_lines(File, Lines), 
  maplist_try(line_rup(Pfx), Lines, RUPs).
