:- [compile].

% 0 : invertible steps
% 1 : atom processing (close if possible)
% 2 : non-invertible steps

/*
strip_pars(Var, Var) :-
  var(Var).

strip_pars(Atom, Atom) :-
  atom(Atom).

strip_pars(@(Num, _), @(Num)).

strip_pars(Exp, NewExp) :-
  \+ var(Exp),
  Exp \= @(_, _), 
  Exp =.. [Sym | Terms], 
  maplist_cut(strip_pars, Terms, NewTerms), 
  NewExp =.. [Sym | NewTerms].

b_d_t(TERMS, NUM, - ! FORM,  - N_FORM) :-
  subst(@(NUM, TERMS), FORM, N_FORM).

b_d_t(TERMS, NUM, + ? FORM,  + N_FORM) :-
  subst(@(NUM, TERMS), FORM, N_FORM).

t_d(
  TERMS,
  (OS, SF),
  (DT, FP, d(ID, Prf)), 
  (NewOS, NewSF),
  (SuccDT, SuccFP, Prf)
) :-
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  SuccFP is FP + 1, 
  b_d_t(FP, TERMS, SF, NewSF).

*/ 

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
  TS = (TERMS, LAS, LFS, RFS, RAS, DFP), 
  pluck(LFS, LA, REST), 
  is_osa(LA),
  N_TS = (TERMS, LAS, REST, RFS, RAS, DFP).

pick_ra(TS, RA, N_TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, DFP), 
  pluck(RFS, RA, REST),
  is_osa(RA),
  N_TS = (TERMS, LAS, LFS, REST, RAS, DFP).

inv_step(OSFS, DFP, [OSF_A, OSF_B | REST], N_DFP) :- 
  pluck(OSFS, OSF, REST),
  i_aa(OSF, DFP, OSF_A, OSF_B, N_DFP).

inv_step(OSFS, DFP, [N_OSF | REST], N_DFP) :- 
  pluck(OSFS, OSF, REST),
  (
    i_n(OSF, DFP, N_OSF, N_DFP) ;
    i_d(OSF, DFP, N_OSF, N_DFP)
  ).

inv_step(
  (TERMS, LAS, LFS, RFS, RAS, DFP), 
  (TERMS, LAS, N_LFS, RFS, RAS, N_DFP)
) :- 
  inv_step(LFS, DFP, N_LFS, N_DFP).

inv_step(
  (TERMS, LAS, LFS, RFS, RAS, DFP), 
  (TERMS, LAS, LFS, N_RFS, RAS, N_DFP)
) :- 
  inv_step(RFS, DFP, N_RFS, N_DFP).

pick_mate_nu(
  (_, _, LFS, _, RAS, DFP) 
) :- 
  member(LA, LFS), 
  is_osa(LA), 
  member(RA, RAS), 
  mate_nu(LA, RA, DFP).

pick_mate_nu(
  (_, LAS, _, RFS, _, DFP) 
) :- 
  member(RA, RFS), 
  is_osa(RA), 
  member(LA, LAS), 
  mate_nu(LA, RA, DFP).

tblx0(TS) :- 
  inv_step(TS, N_TS) -> tblx0(N_TS) ;
  pick_mate_nu(TS) -> true ;
  tblx1(TS).

tblx1(TS) :- 
  pick_la(TS, LA, N_TS) -> tblx1(l, LA, N_TS) ; 
  pick_ra(TS, RA, N_TS) -> tblx1(r, RA, N_TS) ; 
  tblx2(TS).

tblx1(l, LA, TS) :- 
  TS = (INSTS, _, _, _, RAS, DFP), 
  member(RA, RAS), 
  mate(LA, RA, DFP), 
  maplist_cut(check_inst, INSTS).

tblx1(l, LA, TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, DFP), 
  tblx0((TERMS, [LA | LAS], LFS, RFS, RAS, DFP)). 

tblx1(r, RA, TS) :- 
  TS = (INSTS, LAS, _, _, _, DFP), 
  member(LA, LAS), 
  mate(LA, RA, DFP),
  maplist_cut(check_inst, INSTS).

tblx1(r, RA, TS) :- 
  TS = (TERMS, LAS, LFS, RFS, RAS, DFP), 
  tblx0((TERMS, LAS, LFS, RFS, [RA | RAS], DFP)). 

tblx2((TERMS, LAS, LFS, RFS, RAS, DFP)) :- 
  pluck(LFS, LF, REST),
  i_b(LF, DFP, LF0, DFP0, LF1, DFP1), 
  tblx0((TERMS, LAS, [LF0 | REST], RFS, RAS, DFP0)), 
  tblx0((TERMS, LAS, [LF1 | REST], RFS, RAS, DFP1)). 

tblx2((TERMS, LAS, LFS, RFS, RAS, DFP)) :- 
  pluck(RFS, RF, REST),
  i_b(RF, DFP, RF0, DFP0, RF1, DFP1), 
  tblx0((TERMS, LAS, LFS, [RF0 | REST], RAS, DFP0)), 
  tblx0((TERMS, LAS, LFS, [RF1 | REST], RAS, DFP1)). 

tblx2((INSTS, LAS, LFS, RFS, RAS, DFP)) :- 
  DFP = (_, FP, _),
  pluck(LFS, LF, REST),
  i_c(TERM, LF, DFP, N_LF, N_DFP), 
  tblx0(([(TERM, FP) | INSTS], LAS, [N_LF | REST], RFS, RAS, N_DFP)). 

tblx2((INSTS, LAS, LFS, RFS, RAS, DFP)) :- 
  DFP = (_, FP, _),
  pluck(RFS, RF, REST),
  i_c(TERM, RF, DFP, N_RF, N_DFP), 
  tblx0(([(TERM, FP) | INSTS], LAS, LFS, [N_RF | REST], RAS, N_DFP)).

tblx(OSFS_A, OSFS_B, DFP) :- 
  tblx0(([], [], OSFS_A, OSFS_B, [], DFP)). 