:- [basic].

b_a(l, + Form & _, + Form).
b_a(r, + _ & Form, + Form).
b_a(l, - Form | _, - Form).
b_a(r, - _ | Form, - Form).
b_a(l, - Form => _, + Form).
b_a(r, - _ => Form, - Form).
b_a(l, + FormA <=> FormB, + FormA => FormB).
b_a(r, + FormA <=> FormB, + FormB => FormA).

b_aa(SF, SF0, SF1) :-
  b_a(l, SF, SF0), 
  b_a(r, SF, SF1).

b_b(- FormA & FormB, - FormA, - FormB).
b_b(+ FormA | FormB, + FormA, + FormB).
b_b(+ FormA => FormB, - FormA, + FormB).
b_b(- FormA <=> FormB, - FormA => FormB, - FormB => FormA).

b_c(Term, + ! Form, + NewForm) :- 
  subst(Term, Form, NewForm).
b_c(Term, - ? Form, - NewForm) :- 
  subst(Term, Form, NewForm).

b_d(Num, - ! Form,  - NewForm) :-
  subst(@(Num), Form, NewForm).
b_d(Num, + ? Form,  + NewForm) :-
  subst(@(Num), Form, NewForm).

b_n(+ ~ Form, - Form).
b_n(- ~ Form, + Form).

g_a(
  Dir,
  Pos,
  (Ctx, FP, a(Dir, Pos, Prf)), 
  ([NewSF | Ctx], FP, Prf)
) :- 
  nth0(Pos, Ctx, SF),
  b_a(Dir, SF, NewSF).

g_b(
  Pos,
  (Ctx, FP, b(Pos, PrfL, PrfR)), 
  ([SF_L | Ctx], FP, PrfL),
  ([SF_R | Ctx], FP, PrfR)
) :- 
  nth0(Pos, Ctx, SF),
  b_b(SF, SF_L, SF_R).

g_c(
  Term, 
  Pos, 
  (Ctx, FP, c(Term, Pos, Prf)), 
  ([NewSF | Ctx], FP, Prf)
) :- 
  ground(Term), % No logic variables in Term
  ovar_free_term(Term), % No object variables in Term
  no_new_par(FP, Term), % No new parameters in Term
  nth0(Pos, Ctx, SF),
  b_c(Term, SF, NewSF).

g_d(
  Pos,
  (Ctx, FP, d(Pos, Prf)), 
  ([NewSF | Ctx], SuccFP, Prf)
) :-
  nth0(Pos, Ctx, SF),
  SuccFP is FP + 1, 
  b_d(FP, SF, NewSF).

g_f(
  Form,
  (Ctx, FP, f(Form, PrfA, PrfB)), 
  ([- Form | Ctx], FP, PrfA), 
  ([+ Form | Ctx], FP, PrfB)
) :-
  ground(Form), % No logic variables in Form
  closed_form(Form), % No free object variables in Form
  no_new_par(FP, Form). % No new parameters in Form

g_h(
  SF, 
  Jst,
  (Ctx, FP, h(SF, Jst, Prf)),
  ([SF | Ctx], FP, Prf)
) :- 
  no_new_par(FP, SF), % No new parameters in SF
  justified(Ctx, SF, Jst).

g_n(
  Pos, 
  (Ctx, FP, n(Pos, Prf)), 
  ([NewSF | Ctx], FP, Prf)
) :- 
  nth0(Pos, Ctx, SF),
  b_n(SF, NewSF).
 
g_x(Pdx, Ndx, (Ctx, _, x(Pdx, Ndx))) :-
  nth0(Pdx, Ctx, + FormA),
  nth0(Ndx, Ctx, - FormB),
  FormA == FormB.

i_a(
  Dir, 
  (OS, SF),
  (DT, FP, a(Dir, ID, Prf)), 
  (NewOS, NewSF), 
  (SuccDT, FP, Prf)
) :- 
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  b_a(Dir, SF, NewSF).

i_b(
  (OS, SF), 
  (DT, FP, b(ID, PrfL, PrfR)), 
  (NewOS, SF_L),
  (SuccDT, FP, PrfL),
  (NewOS, SF_R),
  (SuccDT, FP, PrfR)
) :- 
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  b_b(SF, SF_L, SF_R). 

i_c(
  Term, 
  (OS, SF), 
  (DT, FP, c(Term, ID, Prf)), 
  (NewOS, NewSF),
  (SuccDT, FP, Prf)
) :- 
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  b_c(Term, SF, NewSF).

i_d(
  (OS, SF),
  (DT, FP, d(ID, Prf)), 
  (NewOS, NewSF),
  (SuccDT, SuccFP, Prf)
) :-
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  SuccFP is FP + 1, 
  b_d(FP, SF, NewSF).

i_f(
  Form,
  (DT, FP, f(Form, PrfA, PrfB)), 
  (NewOS, (- Form)),
  (SuccDT, FP, PrfA), 
  (NewOS, (+ Form)),
  (SuccDT, FP, PrfB)
) :-
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT.

i_h(
  SF,
  Jst,
  (DT, FP, h(SF, Jst, Prf)),
  (NewOS, SF),
  (SuccDT, FP, Prf)
) :- 
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT.

i_n(
  (OS, SF),
  (DT, FP, n(ID, Prf)), 
  (NewOS, NewSF),
  (SuccDT, FP, Prf)
) :- 
  SuccDT is DT + 1, 
  NewOS is 0 - SuccDT,
  ID is DT + OS,
  b_n(SF, NewSF).

i_x(
  (POS, (+ FormP)), 
  (NOS, (- FormN)), 
  (DT, _, x(PID, NID))
) :-
  unify_with_occurs_check(FormP, FormN),
  PID is DT + POS,
  NID is DT + NOS.

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

justified(_, - $false, neg_false). 
justified(_, + $true, pos_true). 

justified(_, + Form, mono_rel(Rel, Num)) :- 
  mk_mono_args(Num, ArgsA, ArgsB),
  AtomA =.. [Rel | ArgsA],
  AtomB =.. [Rel | ArgsB],
  mono_body(Num, Form, AtomA <=> AtomB), !.

justified(_, + Form, mono_fun(Fun, Num)) :- 
  mk_mono_args(Num, ArgsA, ArgsB),
  mono_body(Num, Form, (Fun ^ ArgsA) = (Fun ^ ArgsB)), !.

justified(_, + ((FunA ^ []) = (FunB ^ [])), ne_eval) :- 
  atom_number(FunA, NumA),
  atom_number(FunB, NumB),
  NumA \= NumB.

justified(_, - ((FunA ^ []) = (FunB ^ [])), ne_eval) :- 
  atom_number(FunA, NumA),
  atom_number(FunB, NumB),
  NumA \= NumB.

justified(_, + ! (#(0) = #(0)), refl_eq).
justified(_, + (! ! ((#(1) = #(0)) => (#(0) = #(1)))), symm_eq).
justified(_, + (! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0))))), trans_eq).

justified(Ctx, + Form, aoc(Skm)) :- 
  \+ sub_term(Skm, Ctx), 
  strip_fas(Form, Num, (? Ante) => Cons), 
  \+ sub_term(Skm, Ante), 
  mk_skm_term(Skm, Num, SkmTerm),
  subst(SkmTerm, Ante, NewAnte),
  NewAnte == Cons.

justified(Ctx, + Form, def(Prd)) :- 
  \+ sub_term(Prd, Ctx), 
  strip_fas(Form, Num, Atom <=> Cons), 
  \+ sub_term(Prd, Cons), 
  mk_def_atom(Prd, Num, Atom).