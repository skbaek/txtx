:- [basic].

b_a(l, + FORM & _, + FORM).
b_a(r, + _ & FORM, + FORM).
b_a(l, - FORM | _, - FORM).
b_a(r, - _ | FORM, - FORM).
b_a(l, - FORM => _, + FORM).
b_a(r, - _ => FORM, - FORM).
b_a(l, + FORM_A <=> FORM_B, + FORM_A => FORM_B).
b_a(r, + FORM_A <=> FORM_B, + FORM_B => FORM_A).

b_aa(SF, SF0, SF1) :-
  b_a(l, SF, SF0), 
  b_a(r, SF, SF1).

b_b(- FORM_A & FORM_B, - FORM_A, - FORM_B).
b_b(+ FORM_A | FORM_B, + FORM_A, + FORM_B).
b_b(+ FORM_A => FORM_B, - FORM_A, + FORM_B).
b_b(- FORM_A <=> FORM_B, - FORM_A => FORM_B, - FORM_B => FORM_A).

b_c(TERM, + ! FORM, + NewFORM) :- 
  subst(TERM, FORM, NewFORM).
b_c(TERM, - ? FORM, - NewFORM) :- 
  subst(TERM, FORM, NewFORM).

b_d(NUM, - ! FORM,  - NewFORM) :-
  subst(@(NUM), FORM, NewFORM).
b_d(NUM, + ? FORM,  + NewFORM) :-
  subst(@(NUM), FORM, NewFORM).

b_n(+ ~ FORM, - FORM).
b_n(- ~ FORM, + FORM).

as(
  WRT,
  PID,
  CID,
  DIR,
  (CTX, FP), 
  (CTX_N, FP)
) :- 
  get_assoc(PID, CTX, SF),
  b_a(DIR, SF, SF_N),
  put_assoc(CID, CTX, SF_N, CTX_N),
  (
    WRT = some(STRM) -> (
      put_atom(STRM, DIR), 
      put_atom(STRM, CID),
      put_atom(STRM, PID), 
      put_char_end(STRM, 'a')
    ) ; true
  ).

bs(
  WRT,
  PID,
  CID,
  (CTX, FP), 
  (CTX_L, FP),
  (CTX_R, FP)
) :- 
  get_assoc(PID, CTX, SF),
  b_b(SF, SF_L, SF_R),
  put_assoc(CID, CTX, SF_L, CTX_L),
  put_assoc(CID, CTX, SF_R, CTX_R),
  (
    WRT = some(STRM) -> (
      put_atom(STRM, CID),
      put_atom(STRM, PID), 
      put_char_end(STRM, 'b')
    ) ; true
  ).

cs(
  WRT, 
  PID, 
  CID, 
  TERM, 
  (CTX, FP), 
  (CTX_N, FP)
) :- 
  ground(TERM), % No logic variables in TERM
  ovar_free_term(TERM), % No free object variables in TERM
  no_new_par(FP, TERM), % No new parameters in TERM
  get_assoc(PID, CTX, SF),
  b_c(TERM, SF, SF_N), 
  put_assoc(CID, CTX, SF_N, CTX_N),
  (
    WRT = some(STRM) -> (
      put_term(STRM, TERM),
      put_atom(STRM, CID),
      put_atom(STRM, PID), 
      put_char_end(STRM, 'c')
    ) ; true
  ).

ds(
  WRT,
  PID, 
  CID, 
  (CTX, FP), 
  (CTX_N, SUCC)
) :-
  get_assoc(PID, CTX, SF),
  SUCC is FP + 1, 
  b_d(FP, SF, SF_N), 
  put_assoc(CID, CTX, SF_N, CTX_N),
  (
    WRT = some(STRM) -> (
      put_atom(STRM, CID),
      put_atom(STRM, PID), 
      put_char_end(STRM, 'd')
    ) ; true
  ).

ks(
  WRT,
  CID,
  FORM,
  (CTX, FP), 
  (CTX_L, FP), 
  (CTX_R, FP)
) :-
  ground(FORM), % No logic variables in Form
  closed_form(FORM), % No free object variables in Form
  no_new_par(FP, FORM), % No new parameters in Form
  put_assoc(CID, CTX, - FORM, CTX_L),
  put_assoc(CID, CTX, + FORM, CTX_R),
  (
    WRT = some(STRM) -> (
      put_form(STRM, FORM), 
      put_atom(STRM, CID),
      put_char_end(STRM, 'k')
    ) ; true
  ).

ts(
  WRT,
  CID,
  SF, 
  JST,
  (CTX, FP),
  (CTX_N, FP)
) :- 
  no_new_par(FP, SF), % No new parameters in SF
  justified(CTX, SF, JST),
  put_assoc(CID, CTX, SF, CTX_N),
  (
    WRT = some(STRM) -> (
      put_strings(STRM, JST),
      put_sf(STRM, SF),
      put_atom(STRM, CID),
      put_char_end(STRM, 't')
    ) ; true
  ).

ns(
  WRT,
  PID, 
  CID, 
  (CTX, FP),
  (CTX_N, FP)
) :- 
  get_assoc(PID, CTX, SF),
  b_n(SF, SF_N),
  put_assoc(CID, CTX, SF_N, CTX_N),
  (
    WRT = some(STRM) -> (
      put_atom(STRM, CID),
      put_atom(STRM, PID), 
      put_char_end(STRM, 'n')
    ) ; true
  ).
 
xs(WRT, PID, NID, (CTX, _)) :-
  get_assoc(PID, CTX, + FORM_A),
  get_assoc(NID, CTX, - FORM_B),
  FORM_A == FORM_B, 
  (
    WRT = some(STRM) -> (
      put_atom(STRM, NID),
      put_atom(STRM, PID),
      put_char_end(STRM, 'x')
    ) ; true
  ).

ap(
  DIR, 
  (PID, SF),
  (a(PID, CID, DIR, PRF), FP, FI), 
  (CID, SF_N), 
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  atom_concat(x, FI, CID),
  b_a(DIR, SF, SF_N).

bp(
  (PID, SF), 
  (b(PID, CID, PRF_A, PRF_B), FP, FI), 
  (CID, SF_L),
  (PRF_A, FP, FI_N),
  (CID, SF_R),
  (PRF_B, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  atom_concat(x, FI, CID),
  b_b(SF, SF_L, SF_R). 

cp(
  TERM, 
  (PID, SF), 
  (c(PID, CID, TERM, PRF), FP, FI), 
  (CID, SF_N),
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  atom_concat(x, FI, CID),
  b_c(TERM, SF, SF_N).

dp(
  (PID, SF),
  (d(PID, CID, PRF), FP, FI), 
  (CID, SF_N),
  (PRF, FP_N, FI_N)
) :-
  FP_N is FP + 1, 
  FI_N is FI + 1, 
  atom_concat(x, FI, CID),
  b_d(FP, SF, SF_N).

kp(
  FORM,
  (k(CID, FORM, PRF_A, PRF_B), FP, FI), 
  (CID, (- FORM)),
  (PRF_A, FP, FI_N), 
  (CID, (+ FORM)),
  (PRF_B, FP, FI_N)
) :-
  atom_concat(x, FI, CID),
  FI_N is FI + 1.

tp(
  SF,
  JST,
  (t(CID, SF, JST, PRF), FP, FI),
  (CID, SF),
  (PRF, FP, FI_N)
) :- 
  atom_concat(x, FI, CID),
  FI_N is FI + 1.

np(
  (PID, SF),
  (n(PID, CID, PRF), FP, FI), 
  (CID, SF_N),
  (PRF, FP, FI_N)
) :- 
  atom_concat(x, FI, CID),
  FI_N is FI + 1,
  b_n(SF, SF_N).

xp(
  (PID, (+ FORM_P)), 
  (NID, (- FORM_N)), 
  (x(PID, NID), _, _)
) :-
  unify_with_occurs_check(FORM_P, FORM_N).

type_sf(a, SF) :- 
  b_a(l, SF, _).

type_sf(b, SF) :- 
  b_b(SF, _, _).

type_sf(c, SF) :- 
  b_c(_, SF, _).

type_sf(d, SF) :- 
  b_d(_, SF, _).

type_sf(n, SF) :- 
  b_n(SF, _).

type_osf(Type, (_, SF)) :- 
  type_sf(Type, SF).

justified(_, - $false, ["neg-false"]). 
justified(_, + $true, ["pos-true"]). 

justified(_, + FORM, ["mono-rel", REL_STR, NUM_STR]) :- 
  atom_string(REL, REL_STR),
  number_string(NUM, NUM_STR),
  mk_mono_args(NUM, ArgsA, ArgsB),
  AtomA =.. [REL | ArgsA],
  AtomB =.. [REL | ArgsB],
  mono_body(NUM, FORM, AtomA <=> AtomB), !.

justified(_, + FORM, ["mono-fun", FUN_STR, NUM_STR]) :- 
  atom_string(FUN, FUN_STR),
  number_string(NUM, NUM_STR),
  mk_mono_args(NUM, ArgsA, ArgsB),
  mono_body(NUM, FORM, (FUN ^ ArgsA) = (FUN ^ ArgsB)), !.

justified(_, + ((FUNA ^ []) = (FUNB ^ [])), ["ne-eval"]) :- 
  atom_number(FUNA, NUMA),
  atom_number(FUNB, NUMB),
  NUMA \= NUMB.

justified(_, - ((FUNA ^ []) = (FUNB ^ [])), ["ne-eval"]) :- 
  atom_number(FUNA, NUMA),
  atom_number(FUNB, NUMB),
  NUMA \= NUMB.

justified(_, + ! (#(0) = #(0)), ["refl-eq"]).
justified(_, + (! ! ((#(1) = #(0)) => (#(0) = #(1)))), ["symm-eq"]).
justified(_, + (! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0))))), ["trans-eq"]).

justified(CTX, + FORM, ["aoc", SKM_STR]) :- 
  atom_string(SKM, SKM_STR),
  \+ sub_term(SKM, CTX), 
  strip_fas(FORM, NUM, (? Ante) => Cons), 
  \+ sub_term(SKM, Ante), 
  mk_skm_term(SKM, NUM, SKM_TERM),
  subst(SKM_TERM, Ante, NewAnte),
  NewAnte == Cons.

justified(CTX, + FORM, ["def", PRD_STR]) :- 
  atom_string(PRD, PRD_STR),
  \+ sub_term(PRD, CTX), 
  strip_fas(FORM, NUM, Atom <=> Cons), 
  \+ sub_term(PRD, Cons), 
  mk_def_atom(PRD, NUM, Atom).