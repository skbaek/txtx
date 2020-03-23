:- op(1200,  fy, +).   % Positive formula
:- op(1200,  fy, -).   % Negative formula
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, xfy, '|').  % disjunction
:- op(1100, xfy, '~|'). % negated disjunction
:- op(1000, xfy, &).    % conjunction
:- op(1000, xfy, ~&).   % negated conjunction
:- op(500,   fy, ~).    % negation
:- op(500,  xfy, :).
:- op(499,   fy, !).     % universal quantifier
:- op(499,   fy, ?).     % existential quantifier
:- op(499,  xfy, =).
:- op(499,  xfy, \=).

%%%%%%%%%%%%%%%% GENERIC %%%%%%%%%%%%%%%% 
  
random_pluck(LIST, ELEM, REST) :- 
  random_member(ELEM, LIST), 
  delete(LIST, ELEM, REST).

random_plucks(NUM, LIST, ELEMS, REST) :- 
  num_pred(NUM, PRED) -> 
  ELEMS = [ELEM | TAIL], 
  random_pluck(LIST, ELEM, TEMP),
  random_plucks(PRED, TEMP, TAIL, REST) 
; 
  ELEMS = [],
  REST = LIST.

pick_left(([ELEM | LFT], RGT), ELEM, (LFT, RGT)).  
pick_left(([HEAD | LFT], RGT), ELEM, REST) :- 
  pick_left((LFT, [HEAD | RGT]), ELEM, REST).
    
pick_right((LFT, [ELEM | RGT]), ELEM, (LFT, RGT)).  
pick_right((LFT, [HEAD | RGT]), ELEM, REST) :- 
  pick_right(([HEAD | LFT], RGT), ELEM, REST).

pick(BL, ELEM, REST) :- 
  pick_left(BL, ELEM, REST) ;
  pick_right(BL, ELEM, REST).
  
timed_call(Time, GOAL, ALT_GOAL) :- 
  catch(
    call_with_time_limit(
      Time, 
      (
        call(GOAL) -> 
        true 
      ;
        write("Premature failure in timed call.\n"),
        throw(time_limit_exceeded)
      )
    ),
    time_limit_exceeded, 
    call(ALT_GOAL)
  ).  

eq(X, X).


ground_all(TERM, EXP) :- 
  term_variables(EXP, VARS),
  maplist_cut(eq(TERM), VARS).

pluck_assoc(KEY, ASC_I, VAL, ASC_O) :- 
  gen_assoc(KEY, ASC_I, VAL), 
  del_assoc(KEY, ASC_I, _, ASC_O).

exclude_assoc(GOAL, ASC_I, ASC_O) :- 
  assoc_to_list(ASC_I, LIST_I), 
  exclude(GOAL, LIST_I, LIST_O), 
  list_to_assoc(LIST_O, ASC_O).

range_core(UB, UB, []) :- !.

range_core(NUM, UB, [NUM | NUMS]) :- 
  SUCC is NUM + 1, 
  range_core(SUCC, UB, NUMS).

range(LOW, HIGH, NUMS) :- 
  LOW =< HIGH, 
  range_core(LOW, HIGH, NUMS). 

pluck_unique(List, Elem, Rest) :- 
  pluck_unique([], List, Elem, Rest).

pluck_unique(Acc, [Elem | List], Elem, Rest) :- 
  \+ member_syn(Elem, Acc),
  append(Acc, List, Rest).

pluck_unique(Acc, [Elem | List], Pick, Rest) :- 
  pluck_unique([Elem | Acc], List, Pick, Rest).

%%%%%%%%%%%%%%%% SYNTACTIC %%%%%%%%%%%%%%%% 

type_sf(a, + (_ & _)). 
type_sf(a, - (_ | _)). 
type_sf(a, - (_ => _)). 
type_sf(a, + (_ <=> _)). 
type_sf(b, - (_ & _)). 
type_sf(b, + (_ | _)). 
type_sf(b, + (_ => _)). 
type_sf(b, - (_ <=> _)). 
type_sf(c, + ! _). 
type_sf(c, - ? _). 
type_sf(d, - ! _). 
type_sf(d, + ? _). 
type_sf(s, + ~ _).
type_sf(s, - ~ _).
type_hyp(TYP, (_, SF)) :- type_sf(TYP, SF).
atomic_hyp((_, SF)) :- 
  signed_atom(SF).

sf_form(+ FORM, FORM).
sf_form(- FORM, FORM).
hyp_form((_, SF), FORM) :- 
  sf_form(SF, FORM).

signed_atom(Satom) :- pos_atom(Satom).
signed_atom(Satom) :- neg_atom(Satom).
neg_atom(- ATOM) :- unsigned_atom(ATOM).
pos_atom(+ ATOM) :- unsigned_atom(ATOM).
unsigned_atom(ATOM) :- \+ molecular(ATOM).

complements(+ FORM, - FORM).
complements(- FORM, + FORM).

fof(_, _, _).
fof(_, _, _, _).
cnf(_, _, _).
cnf(_, _, _, _).

hyp_sf((_, SF), SF).

incr_idx(Depth, Idx, #(NewIdx)) :- 
  NewIdx is Idx + Depth.

subst_term(_, _, VAR, VAR) :- var(VAR), !.
subst_term(NUM, TERM, #(NUM), TERM) :- !.
subst_term(_, _, #(NUM), #(NUM)) :- !.
subst_term(_, _, @(NUM), @(NUM)) :- !.
subst_term(NUM, TERM, TERM_IN, TERM_OUT) :- 
  TERM_IN =.. [FUN | TERMS_IN], 
  maplist_cut(subst_term(NUM, TERM), TERMS_IN, TERMS_OUT), 
  TERM_OUT =.. [FUN | TERMS_OUT]. 

qtf('!').
qtf('?').

uct('~').
uct('!').
uct('?').

bct('|').
bct('&').
bct('=>').
bct('<=>').

log_const($true).
log_const($false).

contradiction(- $true).
contradiction(+ $false).

subst_form(_, _, FORM, FORM) :- log_const(FORM), !.

subst_form(NUM, TERM, ~ FORM, ~ FORM_N) :- !,
  subst_form(NUM, TERM, FORM, FORM_N).

subst_form(NUM, TERM, ! FORM, ! FORM_N) :- !,
  SUCC is NUM + 1,
  subst_form(SUCC, TERM, FORM, FORM_N).

subst_form(NUM, TERM, ? FORM, ? FORM_N) :- !, 
  SUCC is NUM + 1,
  subst_form(SUCC, TERM, FORM, FORM_N).

subst_form(NUM, TERM, FORM, FORM_N) :- 
  FORM =.. [BCT, FORM_A, FORM_B], 
  bct(BCT), !, 
  subst_form(NUM, TERM, FORM_A, FORM_AN),
  subst_form(NUM, TERM, FORM_B, FORM_BN),
  FORM_N =.. [BCT, FORM_AN, FORM_BN]. 

subst_form(NUM, TERM, FORM, FORM_N) :- 
  FORM =.. [REL | TERMS], 
  maplist_cut(subst_term(NUM, TERM), TERMS, TERMS_N), 
  FORM_N =.. [REL | TERMS_N]. 

subst_form(TERM, FORM, FORM_N) :- 
  subst_form(0, TERM, FORM, FORM_N).

ab(l, + FORM & _, + FORM).
ab(r, + _ & FORM, + FORM).
ab(l, - FORM | _, - FORM).
ab(r, - _ | FORM, - FORM).
ab(l, - FORM => _, + FORM).
ab(r, - _ => FORM, - FORM).
ab(l, + FORM_A <=> FORM_B, + FORM_A => FORM_B).
ab(r, + FORM_A <=> FORM_B, + FORM_B => FORM_A).

aab(SF, SF0, SF1) :-
  ab(l, SF, SF0), 
  ab(r, SF, SF1).

bb(- FORM_A & FORM_B, - FORM_A, - FORM_B).
bb(+ FORM_A | FORM_B, + FORM_A, + FORM_B).
bb(+ FORM_A => FORM_B, - FORM_A, + FORM_B).
bb(- FORM_A <=> FORM_B, - FORM_A => FORM_B, - FORM_B => FORM_A).

cb(TERM, + ! FORM_I, + FORM_O) :- subst_form(TERM, FORM_I, FORM_O).
cb(TERM, - ? FORM_I, - FORM_O) :- subst_form(TERM, FORM_I, FORM_O).

db(NUM, - ! FORM_I,  - FORM_O) :- subst_form(@(NUM), FORM_I, FORM_O).
db(NUM, + ? FORM_I,  + FORM_O) :- subst_form(@(NUM), FORM_I, FORM_O).

dt(TERM, - ! FORM_I,  - FORM_O) :- subst_form(TERM, FORM_I, FORM_O).
dt(TERM, + ? FORM_I,  + FORM_O) :- subst_form(TERM, FORM_I, FORM_O).

sb(+ ~ FORM, - FORM).
sb(- ~ FORM, + FORM).

char_form_sf('+', FORM, + FORM).
char_form_sf('-', FORM, - FORM).

%%%%%%%%%%%%%%%% BASIC RULES %%%%%%%%%%%%%%%% 

ap(
  (PID, SF),
  DIR, 
  (a(PID, DIR, FID, PRF), FP, FID), 
  (FID, SF_N), 
  (PRF, FP, FID_N)
) :- 
  FID_N is FID + 1, 
  ab(DIR, SF, SF_N), !.

bp(
  (PID, SF), 
  (b(PID, FID, PRF_A, PRF_B), FP, FID), 
  (FID, SF_L),
  (FID, SF_R),
  (PRF_A, FP, FID_N),
  (PRF_B, FP, FID_N)
) :- 
  FID_N is FID + 1, 
  bb(SF, SF_L, SF_R), !.

cp(
  (PID, SF), 
  TERM, 
  (c(PID, TERM, FID, PRF), FP, FID), 
  (FID, SF_N),
  (PRF, FP, FID_N)
) :- 
  FID_N is FID + 1, 
  cb(TERM, SF, SF_N), !.

dp(
  (PID, SF),
  (d(PID, FID, PRF), FP, FID), 
  (FID, SF_N),
  (PRF, FP_N, FID_N)
) :-
  FP_N is FP + 1, 
  FID_N is FID + 1, 
  db(FP, SF, SF_N), !.

fp(
  FORM,
  (f(FORM, FID, PRF_A, PRF_B), FP, FID), 
  (FID, (- FORM)),
  (FID, (+ FORM)),
  (PRF_A, FP, FID_N), 
  (PRF_B, FP, FID_N)
) :-
  FID_N is FID + 1, !.

tp(
  SF,
  JST,
  (t(SF, JST, FID, PRF), FP, FID),
  (FID, SF),
  (PRF, FP, FID_N)
) :- 
  FID_N is FID + 1, !.

sp(
  (PID, SF),
  (s(PID, FID, PRF), FP, FID), 
  (FID, SF_N),
  (PRF, FP, FID_N)
) :- 
  FID_N is FID + 1,
  sb(SF, SF_N), !.

wp(
  (PID, _),
  (w(PID, PRF), FP, FID), 
  (PRF, FP, FID)
).

xp(
  (PID, (+ FORM_P)), 
  (NID, (- FORM_N)), 
  (x(PID, NID), _, _)
) :-
  unify_with_occurs_check(FORM_P, FORM_N), !.

justified(_, - $false, [neg_false]). 
justified(_, + $true, [pos_true]). 

justified(_, + FORM, [mono_rel, REL, NUM_ATOM]) :- 
  atom_number(NUM_ATOM, NUM),
  mk_mono_args(NUM, ARGS_A, ARGS_B),
  ATOM_A =.. [REL | ARGS_A],
  ATOM_B =.. [REL | ARGS_B],
  mono_body(NUM, FORM, ATOM_A => ATOM_B), !.

justified(_, + FORM, [mono_fun, FUN, NUM_ATOM]) :- 
  atom_number(NUM_ATOM, NUM),
  mk_mono_args(NUM, ARGS_A, ARGS_B),
  TERM_A =.. [FUN | ARGS_A],
  TERM_B =.. [FUN | ARGS_B],
  mono_body(NUM, FORM, TERM_A = TERM_B), !.

% justified(_, + ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.
% 
% justified(_, - ((FUNA ^ []) = (FUNB ^ [])), [ne_eval]) :- 
%   atom_number(FUNA, NUMA),
%   atom_number(FUNB, NUMB),
%   NUMA \= NUMB.

justified(_, + ! (#(0) = #(0)), [refl_eq]).
justified(_, + (! ! ((#(1) = #(0)) => (#(0) = #(1)))), [symm_eq]).
justified(_, + (! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0))))), [trans_eq]).

justified(CTX, + FORM, [aoc, SKM_STR]) :- 
  atom_string(SKM, SKM_STR),
  \+ sub_term(SKM, CTX), 
  strip_fas(FORM, NUM, (? Ante) => Cons), 
  \+ sub_term(SKM, Ante), 
  mk_skm_term(SKM, NUM, SKM_TERM),
  subst_form(SKM_TERM, Ante, NewAnte),
  NewAnte == Cons.

justified(CTX, + FORM, [def, PRD_STR]) :- 
  atom_string(PRD, PRD_STR),
  \+ sub_term(PRD, CTX), 
  strip_fas(FORM, NUM, Atom <=> Cons), 
  \+ sub_term(PRD, Cons), 
  mk_def_atom(PRD, NUM, Atom).



%%%%%%%%%%%%%%%% DERIVED RULES %%%%%%%%%%%%%%%% 

many(RULS, (HYPS, GOAL), HGS) :-
  member(s, RULS), 
  pluck(HYPS, HYP, REST), 
  sp(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(a, RULS), 
  pluck(HYPS, HYP, REST), 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_T), 
  many(RULS, ([HYP_R, HYP_L | REST], GOAL_T), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(d, RULS), 
  pluck(HYPS, HYP, REST), 
  dp(HYP, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(c, RULS), 
  pluck(HYPS, HYP, REST), 
  cp(HYP, _, GOAL, HYP_N, GOAL_N), !,
  many(RULS, ([HYP_N | REST], GOAL_N), HGS).

many(RULS, (HYPS, GOAL), HGS) :-
  member(b, RULS), 
  pluck(HYPS, HYP, REST), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), !, 
  many(RULS, ([HYP_L | REST], GOAL_L), HGSL), !,
  many(RULS, ([HYP_R | REST], GOAL_R), HGSR),
  append(HGSL, HGSR, HGS). 

many(_, HG, [HG]).

many_nb(RULS, HYPS, GOAL, HYP_NS, GOAL_N) :-
  many(RULS, (HYPS, GOAL), [(HYP_NS, GOAL_N)]).

aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N) :- 
  ap(HYP, l, GOAL, HYP_L, GOAL_T), 
  ap(HYP, r, GOAL_T, HYP_R, GOAL_N). 

abp(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) :- 
  bp(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  ap(HYP_A, l, GOAL_TL, HYP_AL, GOAL_L),
  ap(HYP_A, r, GOAL_TR, HYP_AR, GOAL_R).

% bap(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) :- 
%   abp(HYP1, HYP0, GOAL, HYP1A, HYP0A, GOAL_A, HYP1B, HYP0B, GOAL_B). 

% abp_cf(HYP_A, HYP_B, GOAL, HYP_AR, HYP_BL, GOAL_L, HYP_AL, HYP_BR, GOAL_R) :- 
%   bp(HYP_B, GOAL, HYP_BL, GOAL_T_L, HYP_BR, GOAL_T_R), 
%   ap(r, HYP_A, GOAL_T_L, HYP_AR, GOAL_L),
%   ap(l, HYP_A, GOAL_T_R, HYP_AL, GOAL_R).

% abp_sw(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) :- 
%   abp(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) ;
%   abp_cf(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B).


% bap_cf(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) :- 
%   abp_cf(HYP1, HYP0, GOAL, HYP1A, HYP0A, GOAL_A, HYP1B, HYP0B, GOAL_B). 

% bap_sw(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) :- 
%   bap(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B) ;
%   bap_cf(HYP0, HYP1, GOAL, HYP0A, HYP1A, GOAL_A, HYP0B, HYP1B, GOAL_B).

fps(+ Form, GOAL, ONF, GOAL_N, OPF, GOAL_P) :- 
  fp(Form, GOAL, ONF, OPF, GOAL_N, GOAL_P).

fps(- Form, GOAL, OPF, GOAL_P, ONF, GOAL_N) :- 
  fp(Form, GOAL, ONF, OPF, GOAL_N, GOAL_P).

% cdp(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
%   dp(HYP_D, GOAL, HYP_N_D, GOAL_T), 
%   cp(HYP_C, _, GOAL_T, HYP_N_C, GOAL_N). 

cdp(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  GOAL = (_, FP, _), 
  dp(HYP_D, GOAL, HYP_N_D, GOAL_T), 
  cp(HYP_C, @(FP), GOAL_T, HYP_N_C, GOAL_N). 

cdp_lax(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  dp(HYP_D, GOAL, HYP_N_D, GOAL_T), 
  cp(HYP_C, _, GOAL_T, HYP_N_C, GOAL_N). 
  
% dcp(HYP0, HYP1, GOAL, NEW_HYP0, NEW_HYP1, NEW_GOAL) :- 
%   cdp(HYP1, HYP0, GOAL, NEW_HYP1, NEW_HYP0, NEW_GOAL).

% kss(WRT, CID, (+ FORM), GOAL, SUB_GOAL, MAIN_GOAL) :- 
%   ks(WRT, CID, FORM, GOAL, SUB_GOAL, MAIN_GOAL).
% 
% kss(WRT, CID, (- FORM), GOAL, SUB_GOAL, MAIN_GOAL) :- 
%   ks(WRT, CID, FORM, GOAL, MAIN_GOAL, SUB_GOAL).
alwyas_fail(_, _) :- false.

union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

mark(NUM) :-
  number_string(NUM, NUMStr),
  strings_concat(["Tracing ", NUMStr, "\n"], Msg),
  write(Msg).

repeat(0, _).

repeat(NUM, GOAL) :- 
  0 < NUM, 
  Pred is NUM - 1, 
  call(GOAL),
  repeat(Pred, GOAL).

write_break(NUM, TERM) :-
  write(TERM),
  repeat(NUM, write("\n")).

write_list(_, []).

write_list(Stream, [Elem | List]) :- 
  format(Stream, '~w\n', Elem),
  write_list(Stream, List).

write_list([]).

write_list([Elem | List]) :- 
  format('~w\n', Elem),
  write_list(List).

strings_concat([], "").

strings_concat([Str | Strs], NewStr) :- 
  strings_concat(Strs, TempStr), 
  string_concat(Str, TempStr, NewStr). 

strings_concat_with(_, [], "").

strings_concat_with(_, [Str], Str).

strings_concat_with(Div, [Str | Strs], Result) :-
  strings_concat_with(Div, Strs, TempStr),
  strings_concat([Str, Div, TempStr], Result).
 
% Similar to nth0/2, but avoids instantion.
where(ElemA, [ElemB | _], 0) :- 
  ElemA == ElemB.

where(Elem, [_ | List], NUM) :- 
  where(Elem, List, Pred),
  NUM is Pred + 1.

occurs(Elem, [_ | List]) :-
  occurs(Elem, List).

% Similar to member/2, but avoids instantion.
occurs(ElemA, [ElemB | _]) :- 
  ElemA == ElemB.

occurs(Elem, [_ | List]) :-
  occurs(Elem, List).

write_list_file(Target, List) :-
  open(Target, write, Stream),
  write_list(Stream, List),
  close(Stream).

write_file(Target, TERM) :-
  open(Target, write, Stream),
  write(Stream, TERM),
  close(Stream).

pick(GOAL, [Elem | Rem], Elem, Rem) :- 
  call(GOAL, Elem), !.

pick(GOAL, [ElemA | List], ElemB, [ElemA | Rem]) :- 
  pick(GOAL, List, ElemB, Rem).

find(GOAL, List, Elem) :- 
  pick(GOAL, List, Elem, _).

pluck_uniq(List, Elem, REST) :- 
  pluck_uniq([], List, Elem, REST).

pluck_uniq(Acc, [Elem | List], Elem, REST) :- 
  \+ member(Elem, Acc),
  append(Acc, List, REST).

pluck_uniq(Acc, [Elem | List], Pick, REST) :- 
  pluck_uniq([Elem | Acc], List, Pick, REST).

pluck([Elem | Rem], Elem, Rem).

pluck([ElemA | List], ElemB, [ElemA | Rem]) :- 
  pluck(List, ElemB, Rem).

list_prod([ElemA | ListA], [ElemB | ListB], List, [(ElemA, ElemB) | Prod]) :-
  list_prod([ElemA | ListA], ListB, List, Prod).

list_prod([_ | ListA], [], List, Prod) :- 
  list_prod(ListA, List, List, Prod).

list_prod([], _, _, []).

list_prod(ListA, ListB, Prod) :-
  list_prod(ListA, ListB, ListB, Prod).

first(GOAL, [Elem | _], Result) :-
  call(GOAL, Elem, Result), !.

first(GOAL, [_ | List], Result) :-
  first(GOAL, List, Result).

collect(_, [], []).

collect(GOAL, [Elem | List], Results) :-
  call(GOAL, Elem, Result) -> 
  ( collect(GOAL, List, TempResults),
    Results = [Result | TempResults] ) ; 
  collect(GOAL, List, Results).

any(GOAL, [Elem | _]) :-
  call(GOAL, Elem).

any(GOAL, [_ | List]) :-
  any(GOAL, List).

list_br_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with("\n\n", Strs, Str).
  
list_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with(", ", Strs, Str).

last([Elem], Elem). 

last([_ | List], Elem) :- last(List, Elem). 

num_pred(NUM, Pred) :-
  0 < NUM,
  Pred is NUM - 1.

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

write_file_punct(Filename, TERM) :- 
  term_string(TERM, TermStr),
  string_concat(TermStr, ".", Str),
  write_file(Filename, Str).

prob_id_hyp(PROB, ID, (ID, SF)) :- 
  get_assoc(ID, PROB, SF).

molecular(Exp) :- 
  member(Exp, 
    [ (! _), (? _), (~ _), 
      (_ | _), (_ & _), (_ => _), (_ <=> _) ]).

is_osa((_, SA)) :-
  satom(SA).

satom(Satom) :-
  patom(Satom).

satom(Satom) :-
  natom(Satom).

natom(- Atom) :- 
  uatom(Atom).

patom(+ Atom) :- 
  uatom(Atom).

uatom(Atom) :-
  \+ molecular(Atom).

ulit(~ Atom) :- 
  uatom(Atom).

ulit(Atom) :- 
  Atom \= (~ _),
  uatom(Atom).

ucla(Lit | Cla) :- 
  ulit(Lit),
  ucla(Cla).

% ucla(Lit) :-
%   Lit \= (_ | _), 
%   ulit(Lit).
% 
% uqla(! Form) :- 
%   uqla(Form).
% 
% uqla(Form) :- 
%   Form \= ! _, 
%   ucla(Form).
% 
% sqla(+ Form) :- 
%   uqla(Form).
% 
% sqla(- Form) :- 
%   uqla(Form).
% 
% atom_tptp(TPTP) :- 
%   \+ member(TPTP, 
%     [ (! _ : _), (? _ : _), (~ _), 
%       (_ | _), (_ & _), (_ => _), (_ <=> _) ]).
% 
mono_body(0, Form, Form).

mono_body(NUM, ! ! (#(1) = #(0) => Form), Cons) :- 
  num_pred(NUM, Pred),
  mono_body(Pred, Form, Cons).

maplist_try(_, [], []).

maplist_try(GOAL, [ELEM | LIST], RST) :- 
  call(GOAL, ELEM, NEW_ELEM) -> 
  (
    maplist_try(GOAL, LIST, REST), 
    RST = [NEW_ELEM | REST] 
  ) ; 
  (
    % format('Rejected element : ~w\n', ELEM),
    maplist_try(GOAL, LIST, RST)
  ).

maplist_cut(_, []).

maplist_cut(GOAL, [Elem | List]) :- 
  call(GOAL, Elem), !, 
  maplist_cut(GOAL, List). 

maplist_cut(_, [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, ElemA, ElemB), !, 
  maplist_cut(GOAL, ListA, ListB). 

maplist_cut(_, [], [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC]) :- 
  call(GOAL, ElemA, ElemB, ElemC), !, 
  maplist_cut(GOAL, ListA, ListB, ListC). 

maplist_cut(_, [], [], [], []).

maplist_cut(GOAL, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC], [ElemD | ListD]) :- 
  call(GOAL, ElemA, ElemB, ElemC, ElemD), !, 
  maplist_cut(GOAL, ListA, ListB, ListC, ListD). 

maplist_idx(_, _, []).

maplist_idx(GOAL, NUM, [Elem | List]) :- 
  call(GOAL, NUM, Elem), 
  Succ is NUM + 1,
  maplist_idx(GOAL, Succ, List).

maplist_idx(_, _, [], []).

maplist_idx(GOAL, NUM, [ElemA | ListA], [ElemB | ListB]) :- 
  call(GOAL, NUM, ElemA, ElemB), 
  Succ is NUM + 1,
  maplist_idx(GOAL, Succ, ListA, ListB).

mk_pars(0, []).  

mk_pars(NUM, [@(Pred) | VARS]) :- 
  num_pred(NUM, Pred),
  mk_pars(Pred, VARS). 

mk_var(NUM, #(NUM)).

mk_vars(NUM, VARS) :-
  range(0, NUM, NUMS), 
  maplist_cut(mk_var, NUMS, VARS).

mk_skm_term(SKM, NUM, SKM_TERM) :-
  mk_vars(NUM, VARS), 
  SKM_TERM =.. [SKM | VARS].

mk_def_atom(Prd, NUM, Atom) :-
  mk_vars(NUM, VARS),
  Atom =.. [Prd | VARS].

/* MONOtonicity */

mk_mono_args(0, [], []).

mk_mono_args(NUM, [#(NUMA) | VARSA], [#(NUMB) | VARSB]) :-
  NUMA is (NUM * 2) - 1, 
  NUMB is (NUM * 2) - 2, 
  Pred is NUM - 1,
  mk_mono_args(Pred, VARSA, VARSB).

mk_mono_eq(NUM, FUN, TERM_A = TERM_B) :- 
  mk_mono_args(NUM, VARS_A, VARS_B),
  TERM_A =.. [FUN | VARS_A],
  TERM_B =.. [FUN | VARS_B].

mk_mono_imp(NUM, REL, ATOM_A => ATOM_B) :- 
  mk_mono_args(NUM, VarsA, VarsB),
  ATOM_A =.. [REL | VarsA],
  ATOM_B =.. [REL | VarsB], !.

mk_mono_fun(NUM, FUN, MONO) :- 
  mk_mono_eq(NUM, FUN, Eq), 
  mk_mono(NUM, Eq, MONO), !.

mk_mono_rel(NUM, REL, MONO) :- 
  mk_mono_imp(NUM, REL, IMP), 
  mk_mono(NUM, IMP, MONO).

par_is_fresh(_, Var) :- 
  var(Var).

par_is_fresh(_, Exp) :- 
  atomic(Exp).

par_is_fresh(Par, Exp) :- 
  \+ var(Exp), 
  \+ atomic(Exp),
  Exp = @(NUM),
  NUM < Par.

par_is_fresh(Par, Exp) :- 
  \+ var(Exp), 
  \+ atomic(Exp), 
  Exp \= @(_),
  Exp =.. [_ | Exps], 
  maplist_cut(par_is_fresh(Par), Exps). 

member_rev(Elem, [_ | List]) :-
  member_rev(Elem, List). 

member_rev(Elem, [Elem | _]).

member_syn(ElemA, List) :-
  member(ElemB, List),
  ElemA == ElemB.

member_woc(ElemA, List) :-
  member(ElemB, List),
  unify_with_occurs_check(ElemA, ElemB).
  
mem(Elem, List) :-
  member_syn(Elem, List) -> 
  true ; 
  member_woc(Elem, List).

choose(List, Elem) :- 
  member(Elem, List).

choose_two([ElemA | List], ElemA, ElemB) :- 
  choose(List, ElemB).

choose_two([_ | List], ElemA, ElemB) :- 
  choose_two(List, ElemA, ElemB).

fresh_par(Var, _) :- 
  var(Var),
  write("Error : cannot compute fresh parameter for a logic variable\n"),
  throw(unexpected_logic_variable).

fresh_par(TERM, Succ) :- 
  TERM = @(NUM),
  Succ is NUM + 1.

fresh_par(TERM, 0) :- 
  TERM \= @(_),
  atomic(TERM).

fresh_par(Exp, Par) :- 
  Exp \= @(_),
  \+ atomic(Exp), 
  Exp =.. [_ | Exps], 
  maplist_cut(fresh_par, Exps, NUMs), 
  max_list(NUMs, Par).

no_new_par(FP, Exp) :- 
  fresh_par(Exp, ExpFP),
  ExpFP =< FP.

max(NUMA, NUMB, Max) :-
max_list([NUMA, NUMB], Max).

mk_mono(0, Cons, Cons).

mk_mono(NUM, Cons, ! ! ((#(1) = #(0)) => MONO)) :-
  num_pred(NUM, Pred), 
  mk_mono(Pred, Cons, MONO), !.

map_par(_, #(NUM), #(NUM)) :- !.
map_par(GOAL, @(NUM), TERM) :- !, 
  call(GOAL, NUM, TERM).
map_par(GOAL, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(map_par(GOAL), TERMS_I, TERMS_O),
  TERM_O =.. [FUN | TERMS_O]. 

map_form(_, _, FORM, FORM) :- 
  log_const(FORM), !.

map_form(GOAL, DTH, ~ FORM_I, ~ FORM_O) :- !,
  map_form(GOAL, DTH, FORM_I, FORM_O).
  
map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  FORM_I =.. [QTF, SUB_I], 
  qtf(QTF), !, 
  SUCC is DTH + 1,
  map_form(GOAL, SUCC, SUB_I, SUB_O), 
  FORM_O =.. [QTF, SUB_O]. 

map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  FORM_I =.. [BCT, SUB_AI, SUB_BI], 
  bct(BCT), !, 
  map_form(GOAL, DTH, SUB_AI, SUB_AO), 
  map_form(GOAL, DTH, SUB_BI, SUB_BO), 
  FORM_O =.. [BCT, SUB_AO, SUB_BO]. 

map_form(GOAL, DTH, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I], 
  maplist_cut(call(GOAL, DTH), TERMS_I, TERMS_O),
  FORM_O =.. [REL | TERMS_O]. 
/*
map_var_form(GOAL, NUM, ! Form, ! NewForm) :- 
  Succ is NUM + 1,
  map_var_form(GOAL, Succ, Form, NewForm).

map_var_form(GOAL, NUM, ? Form, ? NewForm) :- 
  Succ is NUM + 1,
  map_var_form(GOAL, Succ, Form, NewForm).

map_var_form(GOAL, NUM, FormA & FormB, NewFormA & NewFormB) :- 
  map_var_form(GOAL, NUM, FormA, NewFormA),
  map_var_form(GOAL, NUM, FormB, NewFormB).

map_var_form(GOAL, NUM, FormA | FormB, NewFormA | NewFormB) :- 
  map_var_form(GOAL, NUM, FormA, NewFormA),
  map_var_form(GOAL, NUM, FormB, NewFormB).

map_var_form(GOAL, NUM, FormA => FormB, NewFormA => NewFormB) :- 
  map_var_form(GOAL, NUM, FormA, NewFormA),
  map_var_form(GOAL, NUM, FormB, NewFormB).

map_var_form(GOAL, NUM, FormA <=> FormB, NewFormA <=> NewFormB) :- 
  map_var_form(GOAL, NUM, FormA, NewFormA),
  map_var_form(GOAL, NUM, FormB, NewFormB).

map_var_form(GOAL, NUM, ~ Form, ~ NewForm) :- 
  map_var_form(GOAL, NUM, Form, NewForm).

map_var_form(_, _, $true, $true).
map_var_form(_, _, $false, $false).

map_var_form(GOAL, NUM, Atom, NewAtom) :- 
  \+ molecular(Atom),
  Atom \= $true,
  Atom \= $false,
  Atom =.. [REL | TERMS_],  
  maplist(map_var_term(call(GOAL, NUM)), TERMS_, NewTERMS_),
  NewAtom =.. [REL | NewTERMS_].

map_var_term(_, Var, Var) :- 
  var(Var). 

map_var_term(GOAL, TERM, Rst) :- 
  \+ var(TERM),
  TERM = #(NUM),
  call(GOAL, NUM, Rst). 

map_var_term(_, TERM, @(NUM)) :- 
  \+ var(TERM),
  TERM = @(NUM).

map_var_term(GOAL, TERM_I, TERM_O) :- 
  \+ var(TERM_I),
  TERM_I =.. [FUN | TERMS_I],  
  maplist(map_var_term(GOAL), TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O].  
  */

orient_dir(OPF, ONF, l, OPF, ONF).
orient_dir(ONF, OPF, r, OPF, ONF).

orient_sign(OPF, ONF, OPF, ONF) :- 
  OPF = (_, (+ _)),
  ONF = (_, (- _)).

orient_sign(ONF, OPF, OPF, ONF) :- 
  OPF = (_, (+ _)),
  ONF = (_, (- _)).

strip_fas(Form, 0, Form) :-
  Form \= (! _).

strip_fas(! Form, NUM, Body) :-
  strip_fas(Form, Pred, Body), 
  NUM is Pred + 1.

inst_with_pars(NUM, ! FORM, CNT, BODY) :- !,
  subst_form(@(NUM), FORM, TEMP), 
  SUCC is NUM + 1, 
  inst_with_pars(SUCC, TEMP, CNT, BODY).

inst_with_pars(NUM, FORM, NUM, FORM).

add_fas(0, Form, Form). 

add_fas(NUM, Form, ! NewForm) :-
  num_pred(NUM, Pred), 
  add_fas(Pred, Form, NewForm).

insert(Elem, Set, NewSet) :- 
  sort([Elem | Set], NewSet).

first_syn([ElemA | List], ElemB, NUM) :- 
  ElemA == ElemB -> 
  NUM = 0 ; 
  (
    first_syn(List, ElemB, Pred),
    NUM is Pred + 1
  ).

swap(GOAL, X, Y, Z) :- 
  call(GOAL, Y, X, Z).

remove_at(0, [_ | List], List). 

remove_at(NUM, [Elem | List], [Elem | REST]) :- 
  num_pred(NUM, Pred), 
  remove_at(Pred, List, REST).

remove_once_syn([ElemA | List], ElemB, List) :- 
  ElemA == ElemB.

remove_once_syn([ElemA | List], ElemB, [ElemA | REST]) :- 
  ElemA \== ElemB,
  remove_once_syn(List, ElemB, REST).

remove_once(GOAL, [Elem | List], NewList) :- 
  call(GOAL, Elem) -> 
  NewList = List ; 
  (
    remove_once(GOAL, List, REST), 
    NewList = [Elem | REST]
  ).
  
fid_hyp(CTX, FIDs, FID, (OS, SF)) :- 
  nth0(OS, FIDs, FID),
  nth0(OS, CTX, SF).

fst((X, _), X).
snd((_, Y), Y).

num_range(0, []). 
num_range(NUM, [Pred | NUMs]) :- 
  num_pred(NUM, Pred),  
  num_range(Pred, NUMs). 

% number_varlet(NUM, "x") :- 0 is NUM mod 6.
% number_varlet(NUM, "y") :- 1 is NUM mod 6.
% number_varlet(NUM, "z") :- 2 is NUM mod 6.
% number_varlet(NUM, "w") :- 3 is NUM mod 6.
% number_varlet(NUM, "v") :- 4 is NUM mod 6.
% number_varlet(NUM, "u") :- 5 is NUM mod 6.
% 
% number_varnum(NUM, Sub) :-
%   Quo is NUM div 6,
%   number_string(Quo, Sub).
% 
% var_atom(NUM, Atom) :-
%   number_letter(NUM, Ltr),
%   number_subscript(NUM, Sub),
%   string_concat(Ltr, Sub, Str),
%   atom_string(Atom, Str).
% 
% fix_variables(_, []).
% 
% fix_variables(NUM, [X | Xs]) :-
%   var_atom(NUM, X),
%   SuccNUM is NUM + 1,
%   fix_variables(SuccNUM, Xs).

stream_strings(STRM, STRS) :-
  read_line_to_string(STRM, STR), 
  (
    STR = end_of_file -> 
    STRS = [] ;
    ( 
      STRS = [STR | REST],
      stream_strings(STRM, REST)
    )
  ).

file_strings(FILE, STRS) :-
  open(FILE, read, STRM), 
  stream_strings(STRM, STRS), 
  close(STRM).

read_lines_core(Stream, Lines) :-
  read_line_to_codes(Stream, Line), 
  (
    Line = end_of_file -> 
    Lines = [] ;
    ( 
      Lines = [Line | REST],
      read_lines_core(Stream, REST)
    )
  ).

read_lines(File, Lines) :-
  open(File, read, Stream), 
  read_lines_core(Stream, Lines), 
  close(Stream).

foldl_cut(_, [], V, V).
foldl_cut(GOAL, [ELEM | LIST], V_I, V_O) :- 
  call(GOAL, ELEM, V_I, V_T), !, 
  foldl_cut(GOAL, LIST, V_T, V_O).

string_split_with(Str, Sep, Fst, Snd) :- 
  string_concat(Fst, REST, Str), 
  string_concat(Sep, Snd, REST). 

string_number(Str, NUM) :- 
  number_string(NUM, Str).

invert_sf(+ FORM, - FORM).
invert_sf(- FORM, + FORM).
   
fof_form(_, $true, $true).
fof_form(_, $false, $false).

fof_form(VARS, ~ TPTP, ~ Form) :- !, 
 fof_form(VARS, TPTP, Form).

fof_form(VARS, ! [Var] : TPTP, ! Form)  :- !,
  fof_form([Var | VARS], TPTP, Form).

fof_form(VARS, ! [Var | Rem] : TPTP, ! Form)  :- !,
  fof_form([Var | VARS], ! Rem : TPTP, Form).

fof_form(VARS, ? [Var] : TPTP, ? Form)  :- !,
  fof_form([Var | VARS], TPTP, Form).

fof_form(VARS, ? [Var | Rem] : TPTP, ? Form)  :- !,
  fof_form([Var | VARS], ? Rem : TPTP, Form).

fof_form(VARS, (TPTP_A \= TPTP_B), FORM) :- !, 
  fof_form(VARS, ~ (TPTP_A = TPTP_B), FORM). 

fof_form(VARS, TPTP_A & TPTP_B, FormA & FormB) :- !,
  fof_form(VARS, TPTP_A, FormA), 
  fof_form(VARS, TPTP_B, FormB).

fof_form(VARS, TPTP_A | TPTP_B, FormA | FormB) :- !,
  fof_form(VARS, TPTP_A, FormA),
  fof_form(VARS, TPTP_B, FormB).

fof_form(VARS, TPTP_A => TPTP_B, FormA => FormB) :- !,
  fof_form(VARS, TPTP_A, FormA), 
  fof_form(VARS, TPTP_B, FormB).

fof_form(VARS, TPTP_A <=> TPTP_B, FormA <=> FormB) :- !,
  fof_form(VARS, TPTP_A, FormA),
  fof_form(VARS, TPTP_B, FormB).

fof_form(VARS, TF_A '~|' TF_B, ~ (FORM_A | FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A),
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A ~& TF_B, ~ (FORM_A & FORM_B)) :- !,
  fof_form(VARS, TF_A, FORM_A),
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TF_A <= TF_B, FORM_B => FORM_A) :- !,
  fof_form(VARS, TF_A, FORM_A),
  fof_form(VARS, TF_B, FORM_B).

fof_form(VARS, TPTP_A <~> TPTP_B, ~ (FormA <=> FormB)) :- !,
  fof_form(VARS, TPTP_A, FormA),
  fof_form(VARS, TPTP_B, FormB).

fof_form(VARS, TPTP, Form) :- 
  TPTP =.. [REL | TPTPs], 
  maplist_cut(tt_term(VARS), TPTPs, TERMS),
  Form =.. [REL | TERMS], !.

tt_term(VARS, Var, #(NUM)) :- 
  var(Var),
  where(Var, VARS, NUM), !.

tt_term(VARS, TT, TERM) :- 
  TT =.. [FUN | TTS], 
  maplist_cut(tt_term(VARS), TTS, TERMS), !,
  TERM =.. [FUN | TERMS].

trim_ops(Src, Tgt) :- 
  read_line_to_string(Src, Line), 
  (
    Line = end_of_file -> 
    true ; 
    (
      re_replace("!="/g, "\\=", Line, Line0), 
      re_replace("~\\?"/g, "~ ?", Line0, Line1), 
      re_replace("~\\!"/g, "~ !", Line1, Line2), 
      re_replace("~~~"/g, "~ ~ ~", Line2, Line3), 
      re_replace("~~"/g, "~ ~", Line3, Line4), 
      write(Tgt, Line4), 
      write(Tgt, "\n"), 
      trim_ops(Src, Tgt)
    )
  ).

no_fv_term(_, VAR) :- var(VAR), !, false.
no_fv_term(CNT, #(NUM)) :- !, NUM < CNT.
no_fv_term(_, @(_)) :- !.
no_fv_term(CNT, TERM) :- 
  TERM =.. [_ | TERMS],
  maplist_cut(no_fv_term(CNT), TERMS).

no_fp_term(_, VAR) :- var(VAR), !, false.
no_fp_term(_, #(_)) :- !.
no_fp_term(FP, @(NUM)) :- !, NUM < FP.
no_fp_term(FP, TERM) :- 
  TERM =.. [_ | TERMS],
  maplist_cut(no_fp_term(FP), TERMS).

no_fp_form(_, $true).
no_fp_form(_, $false). 
no_fp_form(FP, FORM) :- 
  FORM =.. [UCT, SUB], 
  uct(UCT), !,
  no_fp_form(FP, SUB).

no_fp_form(FP, FORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !,
  no_fp_form(FP, FORM_A),
  no_fp_form(FP, FORM_B).

no_fp_form(FP, FORM) :- 
  FORM =.. [_ | TERMS],
  maplist_cut(no_fp_term(FP), TERMS).

no_fp_sf(FP, SF) :- 
  sf_form(SF, FORM),
  no_fp_form(FP, FORM).

trim_consult(FILE) :- 
  dynamic(cnf/3),
  dynamic(cnf/4),
  dynamic(fof/3),
  dynamic(fof/4),
  retractall(cnf(_, _, _)),
  retractall(cnf(_, _, _, _)),
  retractall(fof(_, _, _)),
  retractall(fof(_, _, _, _)),
  open(FILE, read, SRC), 
  atomic_concat(FILE, ".temp", TEMP),
  open(TEMP, write, TGT), 
  trim_ops(SRC, TGT), 
  close(SRC),
  close(TGT),
  consult(TEMP),
  delete_file(TEMP).

hyp_tuple((fof, ID, TYPE, TF)) :- 
  fof(OID, TYPE, TF), 
  atom_concat(p, OID, ID).

hyp_tuple((cnf, ID, TYPE, TF)) :- 
  cnf(OID, TYPE, TF),
  atom_concat(p, OID, ID).

tuple_hyp((LNG, ID, TYPE, TF), (ID, (+ FORM))) :- 
  member(TYPE, [axiom, lemma, hypothesis, definition, negated_conjecture]),
  tf_form(LNG, TF, FORM).

tuple_hyp((LNG, ID, conjecture, TF), (ID, (- FORM))) :- 
  tf_form(LNG, TF, FORM).

tf_form(fof, TF, FORM) :-
  fof_form([], TF, FORM).

tf_form(cnf, TF, FORM) :- 
  term_variables(TF, VARS), 
  length(VARS, NUM),
  fof_form(VARS, TF, TEMP), 
  add_fas(NUM, TEMP, FORM).

add_sign(TYPE, FORM, + FORM) :-
  member(TYPE, [axiom, lemma, hypothesis, definition, negated_conjecture]).

add_sign(conjecture, FORM, - FORM).

hypothesis((ID, SF)) :- 
  (
    cnf(OID, TYPE, TF), LNG = cnf ;
    fof(OID, TYPE, TF), LNG = fof 
  ),
  tf_form(LNG, TF, FORM),
  atom_concat(p, OID, ID), 
  add_sign(TYPE, FORM, SF).

add_hyp((ID, SF), PROB_IN, PROB_OUT) :- 
  put_assoc(ID, PROB_IN, SF, PROB_OUT).

tptp_prob(TPTP, PIDS, PROB) :- 
  trim_consult(TPTP),
  empty_assoc(EMPTY_PROB), 
  findall(HYP, hypothesis(HYP), HYPS), 
  maplist_cut(fst, HYPS, PIDS),
  foldl(add_hyp, HYPS, EMPTY_PROB, PROB).

break_unary_form(~ FORM, "~", FORM).
break_unary_form(! FORM, "!", FORM).
break_unary_form(? FORM, "?", FORM).
break_binary_form(FORM_A & FORM_B, FORM_A, "&", FORM_B).
break_binary_form(FORM_A | FORM_B, FORM_A, "|", FORM_B).
break_binary_form(FORM_A => FORM_B, FORM_A, "=>", FORM_B).
break_binary_form(FORM_A <=> FORM_B, FORM_A, "<=>", FORM_B).

split_at(NUM, LIST, FST, SND) :- 
  split_at(NUM, [], LIST, FST, SND).

split_at(0, ACC, SND, FST, SND) :-
   reverse(ACC, FST).
  
split_at(NUM, ACC, [ELEM | LIST], FST, SND) :-
  num_pred(NUM, PRED), 
  split_at(PRED, [ELEM | ACC], LIST, FST, SND).

char_bct('|', '|').
char_bct('&', '&').
char_bct('>', '=>').
char_bct('=', '<=>').



%%%%%%%%%%%%%%%% PUT %%%%%%%%%%%%%%%% 

put_list(STRM, _, []) :- 
  put_char(STRM, '.').

put_list(STRM, PTR, [ELEM | LIST]) :- 
  put_char(STRM, ';'),
  call(PTR, STRM, ELEM),
  put_list(STRM, PTR, LIST), !.

put_dot(STRM) :-
  put_char(STRM, '.').

put_bytes(_, []).

put_bytes(STRM, [BYTE | BYTES]) :- 
  put_byte(STRM, BYTE),
  put_bytes(STRM, BYTES).

put_bytes_dot(STRM, BYTES) :- 
  put_bytes(STRM, BYTES), 
  put_dot(STRM). 

put_string(STRM, STR) :- 
  string(STR), 
  string_codes(STR, BYTES),
  put_bytes_dot(STRM, BYTES).

put_atom(STRM, ATOM) :- 
  atom(ATOM), 
  atom_codes(ATOM, BYTES),
  put_bytes_dot(STRM, BYTES).

put_atoms(STRM, ATOMS) :- 
  put_list(STRM, put_atom, ATOMS).

put_strings(STRM, STRS) :- 
  put_list(STRM, put_string, STRS).

put_dir(STRM, l) :- 
  put_char(STRM, "<").

put_dir(STRM, r) :- 
  put_char(STRM, ">").

put_num(STRM, NUM) :- 
  number(NUM),
  number_codes(NUM, BYTES),
  put_bytes_dot(STRM, BYTES).

put_nums(STRM, NUMS) :- 
  put_list(STRM, put_num, NUMS).

nums_id([NUM], NUM) :- !.
nums_id([NUM | NUMS], l(NUM, ID)) :- 
  nums_id(NUMS, ID).

id_nums(l(NUM, ID), [NUM | LIST]) :- !, 
  id_nums(ID, LIST).
id_nums(NUM, [NUM]) :- number(NUM).

put_id(STRM, ID) :- 
  atom(ID) ->  
  put_char(STRM, 'S'),
  put_atom(STRM, ID) ; 
  put_char(STRM, 'N'),
  put_num(STRM, ID).
  
put_term(STRM, #(NUM)) :- !, put_char(STRM, '#'), put_num(STRM, NUM).
put_term(STRM, @(NUM)) :- !, put_char(STRM, '@'), put_num(STRM, NUM).
put_term(STRM, TERM) :- 
  TERM =.. [FUN | TERMS],
  put_char(STRM, '^'), 
  put_atom(STRM, FUN), 
  put_terms(STRM, TERMS). 

put_terms(STRM, TERMS) :- 
  put_list(STRM, put_term, TERMS).

put_form(STRM, $true) :- !,
  put_char(STRM, 'T').

put_form(STRM, $false) :- !, 
  put_char(STRM, 'F').

put_form(STRM, FORM) :- 
  FORM =.. [UCT, SUB], 
  uct(UCT), !,
  put_char(STRM, UCT), 
  put_form(STRM, SUB).

put_form(STRM, FORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  char_bct(CH, BCT), !,
  put_char(STRM, CH), 
  put_form(STRM, FORM_A),
  put_form(STRM, FORM_B).

put_form(STRM, FORM) :- 
  FORM =.. [REL | TERMS],
  put_char(STRM, '^'), 
  put_atom(STRM, REL), 
  put_terms(STRM, TERMS).

put_sf(STRM, SF) :- 
  SF =.. [SIGN, FORM], 
  put_char(STRM, SIGN),
  put_form(STRM, FORM).

put_prf(STRM, a(PID, DIR, CID, PRF)) :- 
  put_char(STRM, 'A'), 
  put_id(STRM, PID), 
  put_dir(STRM, DIR),
  put_id(STRM, CID), 
  put_prf(STRM, PRF).
  
put_prf(STRM, b(PID, CID, PRF_L, PRF_R)) :- 
  put_char(STRM, 'B'), 
  put_id(STRM, PID), 
  put_id(STRM, CID), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, c(PID, TERM, CID, PRF)) :- 
  put_char(STRM, 'C'), 
  put_id(STRM, PID), 
  put_term(STRM, TERM),
  put_id(STRM, CID), 
  put_prf(STRM, PRF).

put_prf(STRM, d(PID, CID, PRF)) :- 
  put_char(STRM, 'D'), 
  put_id(STRM, PID), 
  put_id(STRM, CID), 
  put_prf(STRM, PRF).

put_prf(STRM, f(FORM, CID, PRF_L, PRF_R)) :- 
  put_char(STRM, 'F'), 
  put_form(STRM, FORM), 
  put_id(STRM, CID), 
  put_prf(STRM, PRF_L),
  put_prf(STRM, PRF_R).

put_prf(STRM, s(PID, CID, PRF)) :- 
  put_char(STRM, 'S'), 
  put_id(STRM, PID), 
  put_id(STRM, CID), 
  put_prf(STRM, PRF).

put_prf(STRM, t(SF, JST, CID, PRF)) :- 
  put_char(STRM, 'T'), 
  put_sf(STRM, SF), 
  put_atoms(STRM, JST),
  put_id(STRM, CID), 
  put_prf(STRM, PRF).

put_prf(STRM, w(PID, PRF)) :- 
  put_char(STRM, 'W'), 
  put_id(STRM, PID), 
  put_prf(STRM, PRF).

put_prf(STRM, x(PID, NID)) :- 
  put_char(STRM, 'X'), 
  put_id(STRM, PID), 
  put_id(STRM, NID).


%%%%%%%%%%%%%%%% TACTICS  %%%%%%%%%%%%%%%%

%%%%%%% EQUALITY %%%%%%% 

inst_fas(Form, Form) :-
  Form \= (! _).
  
inst_fas(! Form, Body) :-
  subst_form(_, Form, TempForm),
  inst_fas(TempForm, Body).

term_poseq_term(Var, _) :- 
  var(Var).

term_poseq_term(_, Var) :- 
  var(Var).

term_poseq_term(TERM_A, TERM_B) :- 
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A = @(NUM),
  TERM_B = @(NUM).

term_poseq_term(TERM_A, TERM_B) :- 
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, LTH),
  length(TERMS_B, LTH).

term_poseq_term(_, TERM_A, TERM_B) :- 
  term_poseq_term(TERM_A, TERM_B).

term_poseq_term(OPQEs, TERM_A, TERM_B) :- 
  member((_, (+ QE)), OPQEs), 
  inst_fas(QE, TERM_L = TERM_R), 
  ( 
    term_poseq_term(TERM_A, TERM_L) ; 
    term_poseq_term(TERM_A, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_R) ; 
    term_poseq_term(TERM_B, TERM_L) 
  ).

% eq_refl(CONC, GOAL)
% --- 
% GOAL := ... |- CONC : TERM = TERM, ...
eq_refl(CONC, GOAL) :- 
  tp(+ ! (#(0) = #(0)), [refl_eq], GOAL, HYP0, GOAL_T), 
  cp(HYP0, _, GOAL_T, HYP1, GOAL_N), 
  xp(HYP1, CONC, GOAL_N).

% eq_symm(TERMA, TERMB, GOAL)
% --- 
% GOAL ::= PID : TERMA = TERMB, ... |- NID : TERMB = TERMA, ...
% IPF = PID + TERMA = TERMB
% INF = NID - TERMB = TERMA
eq_symm(OPF, ONF, GOAL) :- 
  OPF = (_, (+ (TERM_A = TERM_B))), 
  ONF = (_, (- (TERM_B = TERM_A))),
  tp(+ ! ! ((#(1) = #(0)) => (#(0) = #(1))), [symm_eq], GOAL, HYP0, GOAL0), 
  cp(HYP0, TERM_A, GOAL0, HYP1, GOAL1), 
  cp(HYP1, TERM_B, GOAL1, HYP2, GOAL2), 
  bp(HYP2, GOAL2, HYP3, HYP4, GOAL3, GOAL4), 
  mate_pn(OPF, HYP3, GOAL3), 
  mate_pn(HYP4, ONF, GOAL4). 

eq_symm(OPF, GOAL, NewOPF, GOAL_N) :- 
  OPF = (_, (+ TERM_A = TERM_B)), 
  fp(TERM_B = TERM_A, GOAL, ONF, NewOPF, GOAL_T, GOAL_N), 
  eq_symm(OPF, ONF, GOAL_T).

% eq_trans(TERM_A, TERM_B, TERM_C, GOAL)
% --- 
% GOAL := PID0 : TERM_A = TERM_B, PID1 : TERM_B = TERM_C, ... |- CID : TERM_A = TERM_C, ...
% IPF0 = PID0 + TERM_A = TERM_B
% IPF1 = PID1 + TERM_B = TERM_C
% INF = NID - TERM_A = TERM_C
eq_trans(IPF0, IPF1, INF, GOAL) :- 
  IPF0 = (_, (+ (TERM_A = TERM_B))), !,
  IPF1 = (_, (+ (TERM_B = TERM_C))), !,
  INF = (_, (- (TERM_A = TERM_C))), !,
  tp(+ ! ! ! ((#(2) = #(1)) => ((#(1) = #(0)) => (#(2) = #(0)))), [trans_eq], GOAL, MONO0, GOAL0),  !,
  cp(MONO0, TERM_A, GOAL0, MONO1, GOAL1), !,
  cp(MONO1, TERM_B, GOAL1, MONO2, GOAL2), !,
  cp(MONO2, TERM_C, GOAL2, MONO3, GOAL3), !,
  bp(MONO3, GOAL3, MONO4, MONO5, GOAL4, GOAL5), !,
  mate(IPF0, MONO4, GOAL4), !,
  bp(MONO5, GOAL5, MONO6, MONO7, GOAL6, GOAL7), !,
  mate(IPF1, MONO6, GOAL6), !,
  mate(INF, MONO7, GOAL7), !.



%%%%%%% Decomposition to Equational GOALs %%%%%%%

intro_eqs(MONO, [], [], GOAL, MONO, [], GOAL).

intro_eqs(MONO, [TERM_A | TERMS_A], [TERM_B | TERMS_B], GOAL, Iff, [(ONE, SubGOAL) | HGS], GOAL_N) :-
  cp(MONO, TERM_A, GOAL, MONOA, GOAL_A), 
  cp(MONOA, TERM_B, GOAL_A, MONOAB, GOAL_AB), 
  bp(MONOAB, GOAL_AB, ONE, TempMONO, SubGOAL, GOAL_T), 
  intro_eqs(TempMONO, TERMS_A, TERMS_B, GOAL_T, Iff, HGS, GOAL_N). 

%break_eq_fun_aux(ONE, MONO, [], [], GOAL, []) :- 
%  mate(ONE, MONO, GOAL).
%
%break_eq_fun_aux(ONEq, MONO, [TERM_A | TERMS_A], [TERM_B |TERMS_B], GOAL, [(NewONEq, GOAL_N) | EGOALs]) :- 
%  cp(TERM_A, MONO, GOAL, MONOA, GOAL_A), 
%  cp(TERM_B, MONOA, GOAL_A, MONOAB, GOAL_AB), 
%  bp(MONOAB, GOAL_AB, NewONEq, TempMONO, GOAL_N, GOAL_T), 
%  break_eq_fun_aux(ONEq, TempMONO, TERMS_A, TERMS_B, GOAL_T, EGOALs). 

break_eq_fun(OPEs, ONE, GOAL, HGS) :- 
  ONE = (_, (- TERM_A = TERM_B)),
  \+ var(TERM_A),
  \+ var(TERM_B),
  TERM_A =.. [FUN | TERMS_A],
  TERM_B =.. [FUN | TERMS_B],
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_fun(LTH, FUN, MONOForm),
  atom_number(LTH_ATOM, LTH),
  tp(+ MONOForm, [mono_fun, FUN, LTH_ATOM], GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, OPE, HGS, GOAL1),
  xp(OPE, ONE, GOAL1).

break_eq_rel(OPEs, OPA, ONA, GOAL, HGS) :- 
  OPA = (_, (+ ATOM_A)),
  ONA = (_, (- ATOM_B)),
  ATOM_A =.. [REL | TERMS_A], 
  ATOM_B =.. [REL | TERMS_B], 
  length(TERMS_A, LTH),
  length(TERMS_B, LTH),
  maplist_cut(term_poseq_term(OPEs), TERMS_A, TERMS_B),
  mk_mono_rel(LTH, REL, MONOForm),
  atom_number(LTH_ATOM, LTH),
  tp(+ MONOForm, [mono_rel, REL, LTH_ATOM], GOAL, MONO, GOAL0),
  intro_eqs(MONO, TERMS_A, TERMS_B, GOAL0, IMP, HGS, GOAL1),
  bp(IMP, GOAL1, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  xp(OPA, HYP_L, GOAL_L), 
  xp(HYP_R, ONA, GOAL_R). 



%%%%%%% Substitution Axiom Application %%%%%%%

subst_fun_single(OPE, (ONE, GOAL)) :- 
  subst_fun_single(OPE, ONE, GOAL). 

subst_fun_single(OPE, ONE, GOAL) :-
  ONE = (_, (- (TERM_A = TERM_B))), 
  (
    TERM_A == TERM_B -> 
    eq_refl(ONE, GOAL) ;
    subst_fun_single_0(OPE, ONE, GOAL)
  ).

subst_fun_single_0(OPE, ONE, GOAL) :-
  OPE = (_, (+ FormA)), 
  ONE = (_, (- FormB)), 
  (
    FormA == FormB ->  
    xp(OPE, ONE, GOAL) ;
    subst_fun_single_1(OPE, ONE, GOAL)
  ).

subst_fun_single_1(_, ONE, GOAL) :-
  ONE = (_, (- (TERM_A = TERM_B))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONE, GOAL).

subst_fun_single_1(OPE, ONE, GOAL) :-
  xp(OPE, ONE, GOAL).

subst_fun_single_1(OPE, ONE, GOAL) :-
  break_eq_fun([OPE], ONE, GOAL, HGS),
  maplist(subst_fun_single(OPE), HGS). 

subst_fun_multi(OPEs, ONE, GOAL, NewOPEs) :-
  ONE = (_, (- (TERM_A = TERM_B))), 
  (
    TERM_A == TERM_B -> 
    (eq_refl(ONE, GOAL), NewOPEs = OPEs) ;
    subst_fun_multi_0(OPEs, ONE, GOAL, NewOPEs)
  ).

subst_fun_multi_0(OPEs, ONF, GOAL, OPEs) :- 
  ONF = (_, (- (TERM_A = TERM_B))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_multi_0(OPEs, ONE, GOAL, NewOPEs) :-
  break_eq_fun(OPEs, ONE, GOAL, HGS),
  subst_fun_multi_aux(OPEs, HGS, NewOPEs). 

subst_fun_multi_0(OPQEs, ONE, GOAL, NewOPQEs) :- 
  ONE = (_, (- (TERM_A0 = TERM_C))), 
  pluck_uniq(OPQEs, OPQE, REST),
  many_nb([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, (+ _ = _)),
  set_dir(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, (+ TERM_A1 = TERM_B)),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_multi(REST, NewONE, GOAL1, NewOPQEs), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_fun_multi_aux(OPEs, [], OPEs).

subst_fun_multi_aux(OPEs, [(ONE, GOAL) | HGS], NewOPEs) :-
  subst_fun_multi(OPEs, ONE, GOAL, TempOPEs),
  subst_fun_multi_aux(TempOPEs, HGS, NewOPEs).
  
% dir_iff(l, l, l).
% dir_iff(l, r, r).
% dir_iff(r, l, r).
% dir_iff(r, r, l).

subst_rel_multi(HYP_L, OPEs, HYP_R, GOAL, NewOPEs) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  % dir_iff(DirA, DirB, Dir),
  set_dir(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(OPEs, OPA, ONA, GOAL_T, HGS),
  subst_fun_multi_aux(OPEs, HGS, NewOPEs). 

subst_rel_single(HYP_L, OPE, HYP_R, GOAL) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  set_dir(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel([OPE], OPA, ONA, GOAL_T, HGS),
  maplist(subst_fun_single(OPE), HGS).

rev_dir(OPF, GOAL, NewOPF, GOAL_N) :- 
  OPF = (_, (+ (TERM_A = TERM_B))), 
  fp(TERM_B = TERM_A, GOAL, NewONF, NewOPF, GOAL_T, GOAL_N), 
  eq_symm(OPF, NewONF, GOAL_T), !. 
 
set_dir(SF, SF).
set_dir(+ (TERM_A = TERM_B), + (TERM_B = TERM_A)).
set_dir(- (TERM_A = TERM_B), - (TERM_B = TERM_A)).

set_dir(OPF, GOAL, OPF, GOAL).

set_dir(OPF, GOAL, NewOPF, GOAL_N) :- 
  rev_dir(OPF, GOAL, NewOPF, GOAL_N).

use_pf(HYP, GOAL) :- 
  HYP = (_, (+ $false)),
  tp(- $false, [neg_false], GOAL, CMP, GOAL_N),
  xp(HYP, CMP, GOAL_N).

use_nt(HYP, GOAL) :- 
  HYP = (_, (- $true)),
  tp(+ $true, [pos_true], GOAL, CMP, GOAL_N),
  xp(CMP, HYP, GOAL_N).

use_lc(HYP, GOAL) :- 
  use_pf(HYP, GOAL) ;
  use_nt(HYP, GOAL).

% mate_tf(HYP, GOAL) :- 
%   use_nt(HYP, GOAL) ;
%   use_pf(HYP, GOAL).
% 
% mate_nu(HYP0, HYP1, GOAL) :- 
%   mate_tf(HYP0, GOAL) ;
%   mate_tf(HYP1, GOAL).
 
mate_nu(HYP0, HYP1, GOAL) :- 
  orient_sign(HYP0, HYP1, OPF, ONF),
  mate_pn_nu(OPF, ONF, GOAL).

% mate(HYP_L, HYP_R, GOAL) :- 
%   mate_tf(HYP_L, GOAL) ;
%   mate_tf(HYP_R, GOAL).

mate(HYP0, HYP1, GOAL) :- 
  orient_sign(HYP0, HYP1, OPF, ONF),
  mate_pn(OPF, ONF, GOAL).
 
% mate(HYP0, HYP1, GOAL) :- 
%   orient(HYP0, HYP1, _, PYP, NYP),
%   mate_pn(PYP, NYP, GOAL).

mate_pn(PYP, NYP, GOAL) :- 
  set_dir(PYP, GOAL, PYP_N, GOAL_N), 
  xp(PYP_N, NYP, GOAL_N).

mate_pn_nu(OPF, ONF, GOAL) :- 
  set_dir(OPF, GOAL, N_OPF, N_GOAL), 
  N_OPF = (_, (+ FORM_A)),
  ONF = (_, (- FORM_B)),
  unifiable(FORM_A, FORM_B, []), 
  xp(N_OPF, ONF, N_GOAL).

connect_sfs(+ FORM_A, - FORM_B) :- 
  connect_forms(FORM_A, FORM_B).
  
connect_sfs(- FORM_A, + FORM_B) :- 
  connect_forms(FORM_A, FORM_B).

connect_forms(FORM_A, FORM_B) :- 
  unify_with_occurs_check(FORM_A, FORM_B).
  
connect_forms(TERM_A = TERM_B, FORM) :- 
  unify_with_occurs_check(TERM_B = TERM_A, FORM).


/*

%%%%%%%%%%%%%%%% DT (DIRECTED TABLEAUX)  %%%%%%%%%%%%%%%%

% 0 : invertible steps
% 1 : atom processing (close if possible)
% 2 : non-invertible steps


pick_la(TS, LA, N_TS) :- 
  TS = (TERMS, LAS, LFC, RFS, RAS, GOAL), 
  pluck(LFC, LA, REST), 
  is_osa(LA),
  N_TS = (TERMS, LAS, REST, RFS, RAS, GOAL).

pick_ra(TS, RA, N_TS) :- 
  TS = (TERMS, LAS, LFC, RFS, RAS, GOAL), 
  pluck(RFS, RA, REST),
  is_osa(RA),
  N_TS = (TERMS, LAS, LFC, REST, RAS, GOAL).

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
  (TERMS, LAS, LFC, RFS, RAS, GOAL), 
  (TERMS, LAS, N_LFC, RFS, RAS, N_GOAL)
) :- 
  inv_step(LFC, GOAL, N_LFC, N_GOAL).

inv_step(
  (TERMS, LAS, LFC, RFS, RAS, GOAL), 
  (TERMS, LAS, LFC, N_RFS, RAS, N_GOAL)
) :- 
  inv_step(RFS, GOAL, N_RFS, N_GOAL).

pick_mate_nu(
  (_, _, LFS, _, RAS, GOAL) 
) :- 
  member(LA, LFS), 
  is_osa(LA), 
  member(RA, RAS), 
  mate_nu(LA, RA, GOAL).

pick_mate_nu(
  (_, LAS, _, RFS, _, GOAL) 
) :- 
  member(RA, RFS), 
  is_osa(RA), 
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
  bp(LF, GOAL, LF0, LF1, GOAL0, GOAL1), 
  tblx0((TERMS, LAS, [LF0 | REST], RFS, RAS, GOAL0)), 
  tblx0((TERMS, LAS, [LF1 | REST], RFS, RAS, GOAL1)). 

tblx2((TERMS, LAS, LFS, RFS, RAS, GOAL)) :- 
  pluck(RFS, RF, REST),
  bp(RF, GOAL, RF0, RF1, GOAL0, GOAL1), 
  tblx0((TERMS, LAS, LFS, [RF0 | REST], RAS, GOAL0)), 
  tblx0((TERMS, LAS, LFS, [RF1 | REST], RAS, GOAL1)). 

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

%%%%%%%%%%%%%%%% AFT (AFFINE FOCUSED TABLEAUX) %%%%%%%%%%%%%%%%

focusable((_, SF)) :- 
  type_sf(b, SF) ;
  type_sf(c, SF) ;
  neg_atom(SF).

later(LVL, (TS, _)) :- LVL < TS.

pick_hyp_from_ctx(CTX, (ID, SF)) :- 
  gen_assoc(ID, CTX, (_, SF)).

del_hyp_from_ctx(CTX_I, (ID, SF), CTX_O) :- 
  del_assoc(ID, CTX_I, (_, SF), CTX_O).
  
add_tm_hyp_to_ctx(TM, (ID, SF), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, (TM, SF), CTX_O).

pick_new_hyp_from_ctx(CTX, HYP) :- 
  pick_new_hyp_from_ctx(CTX, [], HYP).

pick_new_hyp_from_ctx(CTX, ACC, HYP) :- 
  pick_hyp_from_ctx(CTX, (ID, SF)), 
  \+ member_syn(SF, ACC), !, 
  (
    HYP = (ID, SF) ; 
    pick_new_hyp_from_ctx(CTX, [SF | ACC], HYP)
  ).

aft_inv(TM, CTX, GOAL, CTX_N, GOAL_N) :- 
  pick_hyp_from_ctx(CTX, HYP), 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N),
  del_hyp_from_ctx(CTX, HYP, CTX_0),
  add_tm_hyp_to_ctx(TM, HYP_L, CTX_0, CTX_1),
  add_tm_hyp_to_ctx(TM, HYP_R, CTX_1, CTX_N).

aft_inv(TM, CTX, GOAL, CTX_N, GOAL_N) :- 
  pick_hyp_from_ctx(CTX, HYP), 
  (
    sp(HYP, GOAL, HYP_N, GOAL_N) ;
    dp(HYP, GOAL, HYP_N, GOAL_N)
  ), 
  del_hyp_from_ctx(CTX, HYP, CTX_T),
  add_tm_hyp_to_ctx(TM, HYP_N, CTX_T, CTX_N).

aft(CTX, VAL, TM, GOAL, UU) :- 
  aft_inv(TM, CTX, GOAL, CTX_N, GOAL_N), !, 
  aft(CTX_N, VAL, TM, GOAL_N, UU).

aft(CTX, VAL, LVL, GOAL, UU) :- 
  pick_new_hyp_from_ctx(CTX, HYP),
  focusable(HYP),
  del_hyp_from_ctx(CTX, HYP, REST),
  aft(REST, HYP, VAL, LVL, GOAL, UU).
  
aft(CTX, HYP, VAL, TM, GOAL, UU) :- 
  \+ focusable(HYP),
  add_tm_hyp_to_ctx(TM, HYP, CTX, CTX_N),
  aft(CTX_N, VAL, TM, GOAL, UU).

aft(CTX, HYP, VAL, _, GOAL, UU) :- 
  HYP = (_, NA),
  neg_atom(NA), !, 
  pick_new_hyp_from_ctx(CTX, CMP),
  mate(HYP, CMP, GOAL), 
  maplist_cut(check_inst, VAL), 
  del_hyp_from_ctx(CTX, CMP, UU).

% dat((LAC, LFC, RFC, RAS), VAL, LVL, GOAL, UU) :- 
aft(CTX, HYP, VAL, TM, GOAL, UU) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  TM_N is TM + 1,
  aft(CTX, HYP_L, VAL, TM_N, GOAL_L, UU_T), 
  exclude_assoc(later(TM), UU_T, CTX_N), 
  aft(CTX_N, HYP_R, VAL, TM_N, GOAL_R, UU). 

% dat((LAC, LFC, RFC, RAC), VAL, TM, GOAL, UU) :- 
aft(CTX, HYP, VAL, TM, GOAL, UU) :- 
  GOAL = (_, FP, _),
  cp(HYP, TERM, GOAL, HYP_N, GOAL_N), 
  aft(CTX, HYP_N, [(TERM, FP) | VAL], TM, GOAL_N, UU). 
  


%%%%%%%%%%%%%%%% DAFT (DIRECTED AFFINE FOCUSED TABLEAUX) %%%%%%%%%%%%%%%%

daft_focusable((_, _, SF)) :- 
  type_sf(b, SF) ;
  type_sf(c, SF) ;
  neg_atom(SF).

daft_later(TM, (_, TM_H, _)) :- TM < TM_H.

daft_gen(CTX, (DIR, ID, SF)) :- 
  gen_assoc(ID, CTX, (DIR, _, SF)).

daft_del(CTX_I, (ID, SF), CTX_O) :- 
  del_assoc(ID, CTX_I, (_, _, SF), CTX_O).
  
daft_add(DIR, TM, (ID, SF), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, (DIR, TM, SF), CTX_O).

daft_gen_new(CTX, DH) :- 
  daft_gen_new(CTX, [], DH).

daft_gen_new(CTX, ACC, DH) :- 
  daft_gen(CTX, DH_N), 
  \+ member_syn(DH_N, ACC), !, 
  (
    DH = DH_N ;
    daft_gen_new(CTX, [DH_N | ACC], DH)
  ).

daft_inv(TM, CTX, GOAL, CTX_N, GOAL_N) :- 
  daft_gen(CTX, (DIR, HYP)), 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N),
  daft_del(CTX, HYP, CTX_0),
  daft_add(DIR, TM, HYP_L, CTX_0, CTX_1),
  daft_add(DIR, TM, HYP_R, CTX_1, CTX_N).

daft_inv(TM, CTX, GOAL, CTX_N, GOAL_N) :- 
  daft_gen(CTX, (DIR, HYP)), 
  (
    sp(HYP, GOAL, HYP_N, GOAL_N) ;
    dp(HYP, GOAL, HYP_N, GOAL_N)
  ), 
  daft_del(CTX, HYP, CTX_T),
  daft_add(DIR, TM, HYP_N, CTX_T, CTX_N).

daft(CTX, VAL, TM, GOAL, UU) :- 
  daft_inv(TM, CTX, GOAL, CTX_N, GOAL_N), !, 
  daft(CTX_N, VAL, TM, GOAL_N, UU).

daft(CTX, VAL, LVL, GOAL, UU) :- 
  daft_gen(CTX, (DIR, HYP)),
  focusable(HYP),
  daft_del(CTX, HYP, REST),
  daft(REST, (DIR, HYP), VAL, LVL, GOAL, UU).
  
daft(CTX, (DIR, HYP), VAL, TM, GOAL, UU) :- 
  \+ focusable(HYP),
  daft_add(DIR, TM, HYP, CTX, CTX_N),
  daft(CTX_N, VAL, TM, GOAL, UU).

daft(CTX, (DIR_A, HYP), VAL, _, GOAL, UU) :- 
  HYP = (_, NA),
  neg_atom(NA), !, 
  daft_gen_new(CTX, (DIR_B, CMP)),
  DIR_A \= DIR_B,
  mate(HYP, CMP, GOAL), 
  maplist_cut(check_inst, VAL), 
  daft_del(CTX, CMP, UU).

daft(CTX, (DIR, HYP), VAL, TM, GOAL, UU) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  TM_N is TM + 1,
  daft(CTX, (DIR, HYP_L), VAL, TM_N, GOAL_L, UU_T), 
  exclude_assoc(daft_later(TM), UU_T, CTX_N), 
  daft(CTX_N, (DIR, HYP_R), VAL, TM_N, GOAL_R, UU). 

daft(CTX, (DIR, HYP), VAL, TM, GOAL, UU) :- 
  GOAL = (_, FP, _),
  cp(HYP, TERM, GOAL, HYP_N, GOAL_N), 
  daft(CTX, (DIR, HYP_N), [(TERM, FP) | VAL], TM, GOAL_N, UU). 
  
daft(HYP_L, HYP_R, GOAL) :- 
  empty_assoc(EMP),
  daft_add(l, 0, HYP_L, EMP, CTX_T),
  daft_add(r, 0, HYP_R, CTX_T, CTX),
  daft(CTX, [], 0, GOAL, _). 

*/

%%%%%%%%%%%%%%%% TABLEAUX PREDICATES %%%%%%%%%%%%%%%%

bad_inst(TERM, FP) :- 
  sub_term(SUB_TERM, TERM), 
  ground(SUB_TERM),
  SUB_TERM = @(NUM),
  FP =< NUM.

% Check that a term used for gamma rule instantiation 
% does not refer to future parameters

check_inst((TERM, FP)) :- 
  \+ bad_inst(TERM, FP).



%%%%%%%%%%%%%%%% FOCUSED TABLEAUX %%%%%%%%%%%%%%%%

focusable((_, SF)) :- 
  type_sf(c, SF) ;
  neg_atom(SF).

% later(TM, _ - (_, TM_H, _)) :- TM < TM_H.

pick_dh(CTX, (DIR, ID, SF)) :- 
  gen_assoc(ID, CTX, (DIR, SF)).

del_dh(CTX_I, (ID, SF), CTX_O) :- 
  del_assoc(ID, CTX_I, (_, SF), CTX_O).
  
add_dh(DIR, (ID, SF), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, (DIR, SF), CTX_O).

pick_new_dh(CTX, DH) :- 
  pick_new_dh(CTX, [], DH).

pick_new_dh(CTX, ACC, DH) :- 
  pick_dh(CTX, DH_N), 
  \+ member_syn(DH_N, ACC), !, 
  (
    DH = DH_N ;
    pick_new_dh(CTX, [DH_N | ACC], DH)
  ).

tblx_zero(CTX, GOAL) :- 
  pick_dh(CTX, (_, HYP)), 
  use_lc(HYP, GOAL).
  
tblx_one(CTX, GOAL, CTX_N, GOAL_N) :- 
  pick_dh(CTX, (DIR, HYP)), 
  (
    aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N) ->
    del_dh(CTX, HYP, CTX_0),
    add_dh(DIR, HYP_L, CTX_0, CTX_1),
    add_dh(DIR, HYP_R, CTX_1, CTX_N)
  ;
    sp(HYP, GOAL, HYP_N, GOAL_N) ->
    del_dh(CTX, HYP, CTX_T),
    add_dh(DIR, HYP_N, CTX_T, CTX_N)
  ;
    dp(HYP, GOAL, HYP_N, GOAL_N) -> 
    del_dh(CTX, HYP, CTX_T),
    add_dh(DIR, HYP_N, CTX_T, CTX_N)
  ).

tblx_two(CTX, GOAL, CTX_L, GOAL_L, CTX_R, GOAL_R) :- 
  pick_dh(CTX, (DIR, HYP)), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R),
  del_dh(CTX, HYP, CTX_T),
  add_dh(DIR, HYP_L, CTX_T, CTX_L),
  add_dh(DIR, HYP_R, CTX_T, CTX_R).

pick_focus(CTX_I, (DIR, HYP), CTX_O) :- 
  pick_dh(CTX_I, (DIR, HYP)),
  focusable(HYP),
  del_dh(CTX_I, HYP, CTX_O).
  
tblx_focus(OPTS, CTX, (DIR, HYP), VAL, GOAL) :- 
  focusable(HYP) -> 
  (
    tblx_focus_zero(OPTS, CTX, (DIR, HYP), VAL, GOAL) 
  ;
    tblx_focus_one((DIR, HYP), VAL, GOAL, DH_N, VAL_N, GOAL_N),
    tblx_focus(OPTS, CTX, DH_N, VAL_N, GOAL_N)
  )
;
  add_dh(DIR, HYP, CTX, CTX_N),
  tblx(OPTS, CTX_N, VAL, GOAL).

tblx_focus_zero(OPTS, CTX, (DIR_A, HYP), VAL, GOAL) :- 
  HYP = (_, NA),
  neg_atom(NA), 
  pick_new_dh(CTX, (DIR_B, CMP)),
  (
    member(d, OPTS) -> % If proof search is directed
    DIR_A \= DIR_B ;   % Then require different directions
    true
  ),
  mate(HYP, CMP, GOAL), 
  maplist_cut(check_inst, VAL).

tblx_focus_one((DIR, HYP), VAL, GOAL, (DIR, HYP_N), [(TERM, FP) | VAL], GOAL_N) :- 
  GOAL = (_, FP, _),
  cp(HYP, TERM, GOAL, HYP_N, GOAL_N).
  
tblx(OPTS, CTX, VAL, GOAL) :- 
  tblx_zero(CTX, GOAL) -> true ; 
  tblx_one(CTX, GOAL, CTX_N, GOAL_N) -> 
  tblx(OPTS, CTX_N, VAL, GOAL_N) 
; 
  tblx_two(CTX, GOAL, CTX_L, GOAL_L, CTX_R, GOAL_R) -> 
  tblx(OPTS, CTX_L, VAL, GOAL_L), 
  tblx(OPTS, CTX_R, VAL, GOAL_R) 
; 
  pick_focus(CTX, DH, CTX_N),  
  tblx_focus(OPTS, CTX_N, DH, VAL, GOAL).

tblx(HYPS, GOAL) :- 
  empty_assoc(EMP),
  foldl(add_dh(n), HYPS, EMP, CTX),
  tblx([], CTX, [], GOAL). 

tblx(HYP_L, HYP_R, GOAL) :- 
  empty_assoc(EMP),
  add_dh(l, HYP_L, EMP, CTX_T),
  add_dh(r, HYP_R, CTX_T, CTX),
  tblx([d], CTX, [], GOAL). 



%%%%%%%%%%%%%%%% PROPOSITIONAL CONNECTION TABLEAUX %%%%%%%%%%%%%%%%

pick_cla(CTX, (ID, SF)) :- 
  gen_assoc(ID, CTX, SF).

del_cla(CTX_I, (ID, SF), CTX_O) :- 
  del_assoc(ID, CTX_I, SF, CTX_O).
  
add_cla((ID, SF), CTX_I, CTX_O) :- 
  put_assoc(ID, CTX_I, SF, CTX_O).

pluck_cla(CTX_I, CLA, CTX_O) :- 
  pick_cla(CTX_I, CLA),
  del_cla(CTX_I, CLA, CTX_O). 

pos_cla((_, SF)) :- 
  pos_cla_core(SF).

pos_cla_core(CLA) :- 
  CLA = (_, (+ $false)) ;
  CLA = (_, (- $true)) ;
  CLA = (_, (- ~ $false)) ;
  CLA = (_, (+ ~ $true)) ;
  pos_atom(CLA) ; 
  bb(CLA, CLA_L, CLA_R), 
  pos_cla_core(CLA_L),
  pos_cla_core(CLA_R).

pblx(CLAS, GOAL) :- 
  % tp(+ $true, [pos_true], GOAL, TRUE, GOAL_T),
  % tp(- $false, [neg_false], GOAL_T, FALSE, GOAL_N),
  empty_assoc(EMP),
  foldl(add_cla, CLAS, EMP, CTX), !,
  pick_cla(CTX, CLA),
  pos_cla(CLA),
  del_cla(CTX, CLA, REST),
  pblx(block, REST, [], CLA, GOAL).

pblx(MODE, CTX, PATH, CLA, GOAL) :- 
  many([b, s], ([CLA], GOAL), HGS), 
  pblx(MODE, CTX, PATH, HGS).

pblx(block, _, _, []).

pblx(block, CTX, PATH, [([SA], GOAL) | SGS]) :- 
  (
    use_lc(SA, GOAL)  
  ;
    member(CMP, PATH),     % If in block-mode, the signed atom in focus can match with any signed atom on path
    mate(CMP, SA, GOAL)
  ;
    \+ member(SA, PATH), 
    pluck_cla(CTX, CLA, REST),
    pblx(match, REST, [SA | PATH], CLA, GOAL)
  ), !, 
  pblx(block, CTX, PATH, SGS).

pblx(match, CTX, PATH, [([SA], GOAL) | SGS]) :- 
  PATH = [CMP | _],
  mate(CMP, SA, GOAL), 
  pblx(block, CTX, PATH, SGS)
;
  pblx(match, CTX, PATH, SGS), 
  pblx(block, CTX, PATH, [([SA], GOAL)]).



%%%%%%%%%%%%%%%% MATRIX %%%%%%%%%%%%%%%%

replace_skm(SKMS, TERM_I, TERM_O) :- 
  var(TERM_I) -> false 
; 
  TERM_I =.. [FUN | TERMS_I], 
  (
    atom_concat(skm, _, FUN) -> 
    get_assoc(FUN, SKMS, NUM), 
    TERM_O = @(NUM)
  ;  
    maplist_cut(replace_skm(SKMS), TERMS_I, TERMS_O), 
    TERM_O =.. [FUN | TERMS_O]
  ).

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

add_mat((ID, SF), (FI, [(GD, ID, SF) | CTX], [(GD, MAT) | MATS]), (FO, CTX, MATS)) :- 
  matrixify([], (FI, SF), (FO, MAT)).

matrixify_all(HYPS, CTX, MATS) :- 
  foldl(add_mat, HYPS, (0, CTX, MATS), (_, [], [])).

add_to_ctx(HYPS, (ID, GD), CTX_I, CTX_O) :- 
  member((ID, SF), HYPS), 
  put_assoc(ID, CTX_I, (GD, SF), CTX_O).

startable(a(MAT_L, MAT_R)) :- 
  startable(MAT_L) ;
  startable(MAT_R).

startable(b(MAT_L, MAT_R)) :- 
  startable(MAT_L),
  startable(MAT_R).

startable(c(_, MAT)) :- startable(MAT).
startable(d(_, MAT)) :- startable(MAT).
startable(+ _). 

mem_mod_symm(SF, SFS) :- 
  set_dir(SF, SF_N), 
  member_syn(SF_N, SFS).

solve(MATS) :- 
  pluck(MATS, (GD, MAT), REST), 
  solve(start, REST, [], [], (GD, MAT), _).

solve(MODE, MATS, PATH, LEM_I, (a(GD_L, GD_R), a(MAT_L, MAT_R)), LEM_I) :- !, 
  (
    solve(MODE, [(GD_R, MAT_R) | MATS], PATH, LEM_I, (GD_L, MAT_L), _) ;
    solve(MODE, [(GD_L, MAT_L) | MATS], PATH, LEM_I, (GD_R, MAT_R), _)
  ).

solve(start, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  startable(MAT_R),
  solve(start, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
  solve(start, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O).

solve(match, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  (
    solve(match, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
    solve(block, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O)
  ;
    solve(match, MATS, PATH, LEM_I, (GD_R, MAT_R), LEM_T),
    solve(block, MATS, PATH, LEM_T, (GD_L, MAT_L), LEM_O)
  ).
  
solve(block, MATS, PATH, LEM_I, (b(GD_L, GD_R), b(MAT_L, MAT_R)), LEM_O) :- !,
  solve(block, MATS, PATH, LEM_I, (GD_L, MAT_L), LEM_T),
  solve(block, MATS, PATH, LEM_T, (GD_R, MAT_R), LEM_O).

solve(MODE, MATS, PATH, LEM_I, (c(TERM, GD), c(TERM, MAT)), LEM_O) :- !,
  solve(MODE, MATS, PATH, LEM_I, (GD, MAT), LEM_O). 

solve(MODE, MATS, PATH, LEM_I, (d(SKM, GD), d(SKM, MAT)), LEM_O) :- !,
  solve(MODE, MATS, PATH, LEM_I, (GD, MAT), LEM_O). 

solve(match, _, [CMP | _], LEM, (m, SA), LEM) :- 
  connect_sfs(CMP, SA).
  
solve(start, MATS, PATH, LEM_I, (GD, SF), LEM_O) :-
  pos_atom(SF), 
  solve(block, MATS, PATH, LEM_I, (GD, SF), LEM_O).

solve(block, _, _, LEM, (c, SF), LEM) :-
  contradiction(SF).

solve(block, _, _, LEM, (m, SA), LEM) :- 
  mem_mod_symm(SA, LEM), !.

solve(block, _, PATH, LEM, (m, SA), LEM) :- 
  member(CMP, PATH),
  connect_sfs(CMP, SA).

solve(block, MATS, PATH, LEM, (m, SA), [SA | LEM]) :- 
  \+ mem_mod_symm(SA, PATH),
  pluck(MATS, (GD, MAT), REST), 
  solve(match, REST, [SA | PATH], LEM, (GD, MAT), _). 
 
complement_on_path(PATH, HYP, (ID, SA_B)) :- 
  HYP = (_, SA_A),
  complements(SA_A, SA_T),
  set_dir(SA_T, SA_B),
  get_assoc(SA_B, PATH, ID).
 
mtrx_zero((CTX, _, _, GOAL)) :- 
  member((c, HYP), CTX), 
  use_lc(HYP, GOAL).
  
mtrx_zero((CTX, PATH, _, GOAL)) :- 
  member((m, HYP), CTX), 
  atomic_hyp(HYP),
  complement_on_path(PATH, HYP, CMP),
  mate(HYP, CMP, GOAL).

mtrx_one((CTX, PATH, SKMS, GOAL), (REST, PATH, SKMS, GOAL)) :- 
  pluck(CTX, (e, _), REST). 

mtrx_one((CTX, PATH_I, SKMS, GOAL), (REST, PATH_O, SKMS, GOAL)) :- 
  pluck(CTX, (m, HYP), REST), 
  atomic_hyp(HYP),
  HYP = (ID, SA), 
  put_assoc(SA, PATH_I, ID, PATH_O).

mtrx_one((CTX, PATH, SKMS, GOAL), ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N)) :- 
  pluck(CTX, (GD, HYP), REST), 
  sp(HYP, GOAL, HYP_N, GOAL_N).

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD_L, HYP_L), (GD_R, HYP_R) | REST], PATH, SKMS, GOAL_N)
) :- 
  pluck(CTX, (a(GD_L, GD_R), HYP), REST), 
  ap(HYP, l, GOAL, HYP_L, GOAL_T), 
  ap(HYP, r, GOAL_T, HYP_R, GOAL_N). 

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS, GOAL_N) 
) :- 
  pluck(CTX, (c(TERM, GD), HYP), REST), 
  replace_skm(SKMS, TERM, TERM_N), 
  cp(HYP, TERM_N, GOAL, HYP_N, GOAL_N).

mtrx_one(
  (CTX, PATH, SKMS, GOAL), 
  ([(GD, HYP_N) | REST], PATH, SKMS_N, GOAL_N) 
) :- 
  pluck(CTX, (d(SKM, GD), HYP), REST), 
  GOAL = (_, FP, _), 
  put_assoc(SKM, SKMS, FP, SKMS_N), 
  dp(HYP, GOAL, HYP_N, GOAL_N).

mtrx_two(
  (CTX, PATH, SKMS, GOAL), 
  (GD_L, HYP_L), 
  (REST, PATH, SKMS, GOAL_L), 
  (GD_R, HYP_R), 
  (REST, PATH, SKMS, GOAL_R) 
) :- 
  pluck(CTX, (b(GD_L, GD_R), HYP), REST), 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R).

mtrx_fcs(
  (GD, HYP), 
  (CTX, PATH, SKMS, GOAL)
) :- 
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R) -> 
  GD = b(GD_L, GD_R), 
  mtrx_fcs((GD_L, HYP_L), (CTX, PATH, SKMS, GOAL_L)), !,
  mtrx_fcs((GD_R, HYP_R), (CTX, PATH, SKMS, GOAL_R))
;
  mtrx(([(GD, HYP) | CTX], PATH, SKMS, GOAL)).

mtrx(MS) :- 
  mtrx_zero(MS) -> true ; 
  mtrx_one(MS, MS_N) -> mtrx(MS_N) ; 
  mtrx_two(MS, MH_L, MS_L, MH_R, MS_R), !,
  mtrx_fcs(MH_L, MS_L), !, 
  mtrx_fcs(MH_R, MS_R), !. 

mtrx(HYPS, GOAL) :- 
  matrixify_all(HYPS, CTX, MATS),
  solve(MATS), 
  term_variables(CTX, VARS),
  maplist_cut(eq(e), VARS),
  empty_assoc(EMP), !, 
  mtrx((CTX, EMP, EMP, GOAL)).


/*
%%%%%%%%%%%%%%%% DAT (DIRECTED AFFINE TABLEAUX) %%%%%%%%%%%%%%%%

% dat((LAS, LFS, RFC, RAS), VAL, LVL, GOAL, UU)

% F vs. A : any formula vs. atomic & checked
% 1 : non-invertible, atomic steps (closure if possible)
% 2 : non-invertible, non-atomic steps 

has_future_timestamp(LVL, (TS, _)) :- LVL =< TS.

exclude_future_timestamp(
  LVL,
  (LAS_I, LFC_I, RFC_I, LAC_I),
  (LAS_O, LFC_O, RFC_O, LAC_O)
) :- 
  exclude(has_future_timestamp(LVL), LAS_I, LAS_O), 
  exclude(has_future_timestamp(LVL), LFC_I, LFC_O), 
  exclude(has_future_timestamp(LVL), RFC_I, RFC_O), 
  exclude(has_future_timestamp(LVL), LAC_I, LAC_O).

mk_pair(X, Y, (X, Y)).

dat_inv_aux(LVL, THS, GOAL, [(LVL, HYP_A), (LVL, HYP_B) | REST], GOAL_N) :- 
  pluck(THS, (_, HYP), REST),
  aap(HYP, GOAL, HYP_A, HYP_B, GOAL_N).

dat_inv_aux(LVL, THS, GOAL, [(LVL, HYP_N) | REST], GOAL_N) :- 
  pluck(THS, (_, HYP), REST),
  (
    sp(HYP, GOAL, HYP_N, GOAL_N) ;
    dp(HYP, GOAL, HYP_N, GOAL_N)
  ).

dat_inv(
  LVL,
  (LAS, LFC, RFC, LAC), 
  GOAL, 
  (LAS, LFC_N, RFC, LAC), 
  GOAL_N
) :- 
  dat_inv_aux(LVL, LFC, GOAL, LFC_N, GOAL_N).

dat_inv(
  LVL,
  (LAS, LFC, RFC, LAC), 
  GOAL, 
  (LAS, LFC, RFC_N, LAC), 
  GOAL_N
) :- 
  dat_inv_aux(LVL, RFC, GOAL, RFC_N, GOAL_N).

dat(HYPS_A, HYPS_B, GOAL) :- 
  maplist_cut(mk_pair(0), HYPS_A, THS_A),
  maplist_cut(mk_pair(0), HYPS_B, THS_B),
  dat(([], THS_A, THS_B, []), [], 0, GOAL, _). 

dat(CTX, VAL, LVL, GOAL, UU) :-  
  dat_inv(LVL, CTX, GOAL, CTX_N, GOAL_N), !, 
  LVL_N is LVL + 1,
  dat(CTX_N, VAL, LVL_N, GOAL_N, UU).

dat(CTX, VAL, LVL, GOAL, UU) :- 
  CTX = (LAC, LFC, RFC, RAC), 
  pluck(LFC, (TS, LA), LFC_REST),
  is_osa(LA), !, 
  (
    pluck_unique(RAC, (_, RA), RAC_REST),
    mate(LA, RA, GOAL), 
    maplist_cut(check_inst, VAL), 
    UU = (LAC, LFC_REST, RFC, RAC_REST) 
  ;
    CTX_N = ([(TS, LA) | LAC], LFC_REST, RFC, RAC), 
    dat(CTX_N, VAL, LVL, GOAL, UU) 
  ).

dat(CTX, VAL, LVL, GOAL, UU) :- 
  CTX = (LAC, LFC, RFC, RAC), 
  pluck(RFC, (TS, RA), RFC_REST),
  is_osa(RA), !, 
  (
    pluck_unique(LAC, (_, LA), LAC_REST),
    mate(LA, RA, GOAL), 
    maplist_cut(check_inst, VAL), 
    UU = (LAC_REST, LFC, RFC_REST, RAC) 
  ;
    CTX_N = (LAC, LFC, RFC_REST, [(TS, RA) | RAC]), 
    dat(CTX_N, VAL, LVL, GOAL, UU) 
  ).

dat((LAC, LFC, RFC, RAS), VAL, LVL, GOAL, UU) :- 
  pluck_unique(LFC, (_, LF), REST),
  bp(LF, GOAL, LF0, LF1, GOAL0, GOAL1), 
  LVL_N is LVL + 1,
  dat(
    (LAC, [(LVL, LF0) | REST], RFC, RAS), 
    VAL, 
    LVL_N, 
    GOAL0, 
    UU_T
  ), 
  exclude_future_timestamp(
    LVL, 
    UU_T, 
    (LAC_N, LFC_N, RFC_N, RAS_N)
  ),
  dat(
    (LAC_N, [(LVL, LF1) | LFC_N], RFC_N, RAS_N), 
    VAL, 
    LVL_N,
    GOAL1, 
    UU
  ). 

dat((LAC, LFC, RFC, RAS), VAL, LVL, GOAL, UU) :- 
  pluck_unique(RFC, (_, RF), REST),
  bp(RF, GOAL, RF0, RF1, GOAL0, GOAL1), 
  LVL_N is LVL + 1,
  dat(
    (LAC, LFC, [(LVL, RF0) | REST], RAS), 
    VAL, 
    LVL_N, 
    GOAL0, 
    UU_T
  ), 
  exclude_future_timestamp(
    LVL, 
    UU_T, 
    (LAC_N, LFC_N, RFC_N, RAS_N)
  ),
  dat(
    (LAC_N, LFC_N, [(LVL, RF1) | RFC_N], RAS_N), 
    VAL, 
    LVL_N,
    GOAL1, 
    UU
  ). 

dat((LAC, LFC, RFC, RAC), VAL, LVL, GOAL, UU) :- 
  GOAL = (_, FP, _),
  pluck_unique(LFC, (_, LF), REST),
  cp(LF, TERM, GOAL, LF_N, GOAL_N), 
  LVL_N is LVL + 1,
  dat((LAC, [(LVL, LF_N) | REST], RFC, RAC), [(TERM, FP) | VAL], LVL_N, GOAL_N, UU).
  
dat((LAC, LFC, RFC, RAC), VAL, LVL, GOAL, UU) :- 
  GOAL = (_, FP, _),
  pluck_unique(RFC, (_, RF), REST),
  cp(RF, TERM, GOAL, RF_N, GOAL_N), 
  LVL_N is LVL + 1,
  dat((LAC, LFC, [(LVL, RF_N) | REST], RAC), [(TERM, FP) | VAL], LVL_N, GOAL_N, UU).

*/





%%%%%%%% GET %%%%%%%%

get_list(STRM, GTR, LIST) :- 
  get_char(STRM, CH), 
  (
    CH = ';' -> 
    call(GTR, STRM, ELEM), 
    get_list(STRM, GTR, TAIL),
    LIST = [ELEM | TAIL] ;
    CH = '.', 
    LIST = []
  ).

get_until_dot(STRM, BYTES) :- 
  get_byte(STRM, BYTE), 
  (
    BYTE = 46 -> BYTES = [] ;
    get_until_dot(STRM, TAIL),
    BYTES = [BYTE | TAIL] 
  ).
  
get_string(STRM, STR) :- 
  get_until_dot(STRM, BYTES), 
  string_codes(STR, BYTES).
  
get_atom(STRM, ATOM) :- 
  get_string(STRM, STR),
  atom_string(ATOM, STR).
  
get_atoms(STRM, ATOMS) :- 
  get_list(STRM, get_atom, ATOMS).
  
get_num(STRM, NUM) :- 
  get_string(STRM, STR),
  number_string(NUM, STR).

get_nums(STRM, NUMS) :- 
  get_list(STRM, get_num, NUMS).

get_dir(STRM, DIR) :- 
  get_char(STRM, CH),
  (
    CH = '<' -> DIR = l ;
    CH = '>' -> DIR = r
  ).

get_term(STRM, TERM) :- 
  get_char(STRM, CH), 
  get_term(STRM, CH, TERM).

get_term(STRM, '#', #(NUM)) :- get_num(STRM, NUM).
get_term(STRM, '@', @(NUM)) :- get_num(STRM, NUM).
get_term(STRM, '^', TERM) :- 
  get_atom(STRM, FUN), 
  get_terms(STRM, TERMS),
  TERM =.. [FUN | TERMS].

get_terms(STRM, TERMS) :- 
  get_list(STRM, get_term, TERMS).

get_form(STRM, FORM) :-
  get_char(STRM, CH), 
  get_form_aux(STRM, CH, FORM).

get_form_aux(_, 'T', $true).
get_form_aux(_, 'F', $false).

get_form_aux(STRM, '^', FORM) :- 
  get_atom(STRM, REL), 
  get_terms(STRM, TERMS), 
  FORM =.. [REL | TERMS].

get_form_aux(STRM, UCT, FORM) :- 
  uct(UCT), 
  get_form(STRM, SUB), 
  FORM =.. [UCT, SUB].

get_form_aux(STRM, CH, FORM) :- 
  char_bct(CH, BCT), 
  get_form(STRM, SUB_A), 
  get_form(STRM, SUB_B), 
  FORM =.. [BCT, SUB_A, SUB_B].

get_sf(STRM, SF) :- 
  get_char(STRM, SIGN_CH),
  get_form(STRM, FORM),
  char_form_sf(SIGN_CH, FORM, SF).

get_hyp(STRM, (ID, SF)) :- 
  get_atom(STRM, ID), 
  get_sf(STRM, SF). 

get_id(STRM, ID) :- 
  get_char(STRM, CH),
  (
    CH = 'S' -> 
    get_atom(STRM, ID) ;
    CH = 'N' -> 
    get_num(STRM, ID)
  ).

get_prf(STRM, PRF) :- 
  get_char(STRM, CH), 
  (
    CH = 'A' -> 
    PRF = a(PID, DIR, CID, SUB),
    get_id(STRM, PID),  
    get_dir(STRM, DIR),
    get_id(STRM, CID), 
    get_prf(STRM, SUB)  
  ;
    CH = 'B' -> 
    PRF = b(PID, CID, SUB_L, SUB_R),
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB_L), 
    get_prf(STRM, SUB_R) 
  ;
    CH = 'C' -> 
    PRF = c(PID, TERM, CID, SUB),
    get_id(STRM, PID), 
    get_term(STRM, TERM), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB) 
  ;
    CH = 'D' -> 
    PRF = d(PID, CID, SUB),
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB) 
  ;
    CH = 'F' -> 
    PRF = f(FORM, CID, SUB_L, SUB_R),
    get_form(STRM, FORM), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB_L), 
    get_prf(STRM, SUB_R) 
  ;
    CH = 'S' -> 
    PRF = s(PID, CID, SUB),
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB) 
  ;
    CH = 'T' -> 
    PRF = t(SF, JST, CID, SUB),
    get_sf(STRM, SF), 
    get_atoms(STRM, JST), 
    get_id(STRM, CID), 
    get_prf(STRM, SUB) 
  ;
    CH = 'W' -> 
    PRF = w(PID, SUB),
    get_id(STRM, PID), 
    get_prf(STRM, SUB) 
  ;
    CH = 'X' -> 
    PRF = x(PID, NID),
    get_id(STRM, PID), 
    get_id(STRM, NID)
  ).

verify(PROB, FP, a(PID, DIR, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  ab(DIR, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N),
  verify(PROB_N, FP, PRF).

verify(PROB, FP, b(PID, CID, PRF_L, PRF_R)) :- 
  get_assoc(PID, PROB, PREM),
  bb(PREM, CONC_L, CONC_R),
  put_assoc(CID, PROB, CONC_L, PROB_L),
  put_assoc(CID, PROB, CONC_R, PROB_R),
  verify(PROB_L, FP, PRF_L), 
  verify(PROB_R, FP, PRF_R).

verify(PROB, FP, c(PID, TERM, CID, PRF)) :- 
  ground(TERM),
  no_fv_term(0, TERM),
  no_fp_term(FP, TERM),
  get_assoc(PID, PROB, PREM),
  cb(TERM, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N),
  verify(PROB_N, FP, PRF).

verify(PROB, FP, d(PID, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  db(FP, PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N),
  FP_N is FP + 1,
  verify(PROB_N, FP_N, PRF).

verify(PROB, FP, f(FORM, CID, PRF_L, PRF_R)) :- 
  put_assoc(CID, PROB, (- FORM), PROB_L),
  verify(PROB_L, FP, PRF_L),
  put_assoc(CID, PROB, (+ FORM), PROB_R),
  verify(PROB_R, FP, PRF_R).

verify(PROB, FP, s(PID, CID, PRF)) :- 
  get_assoc(PID, PROB, PREM),
  sb(PREM, CONC), 
  put_assoc(CID, PROB, CONC, PROB_N),
  verify(PROB_N, FP, PRF).

verify(PROB, FP, t(SF, JST, CID, PRF)) :- 
  no_fp_sf(FP, SF), % No new parameters in SF
  justified(PROB, SF, JST),
  put_assoc(CID, PROB, SF, PROB_N),
  verify(PROB_N, FP, PRF).
    
verify(PROB, FP, w(PID, PRF)) :- 
  del_assoc(PID, PROB, _, PROB_N),
  verify(PROB_N, FP, PRF).

verify(PROB, _, x(PID, NID)) :- 
  get_assoc(PID, PROB, + FORM_P),
  get_assoc(NID, PROB, - FORM_N),
  FORM_P == FORM_N.



%%%%%%%%%%%%%%%% PARALLEL DECOMPOSITION %%%%%%%%%%%%%%%%
  
para_zero((HYP_A, HYP_B, GOAL)) :- 
  mate(HYP_A, HYP_B, GOAL).

para_one((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  sp(HYP_A, GOAL, HYP_AN, GOAL_N). 
  
para_one((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  sp(HYP_B, GOAL, HYP_BN, GOAL_N). 
  
para_one((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  cdp(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

para_two((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abp(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
  abp(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para_one_lax((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  sp(HYP_A, GOAL, HYP_AN, GOAL_N). 
  
para_one_lax((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  sp(HYP_B, GOAL, HYP_BN, GOAL_N). 
  
para_one_lax((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp_lax(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  cdp_lax(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).



%%%%%%%%%%%%%%%% PARALLEL CLAUSAL DECOMPOSITION %%%%%%%%%%%%%%%%

imp_hyp(HYP) :- 
  hyp_form(HYP, FORM),
  member(FORM, [(_ => _), (_ <=> _)]).

para_cla_a_aux(HYP, GOAL, HYP_L, HYP_R, NEW_GOAL) :- 
  \+ imp_hyp(HYP), 
  ap(HYP, l, GOAL, HYP_L, TEMP_GOAL),
  ap(HYP, r, TEMP_GOAL, HYP_R, NEW_GOAL).

para_cla_a(HYP, GOAL, HYPS, GOAL_N) :- 
  para_cla_a_aux(HYP, GOAL, HYP_L, HYP_R, GOAL0) -> 
  (
    para_cla_a(HYP_L, GOAL0, HYPS_L, GOAL1),
    para_cla_a(HYP_R, GOAL1, HYPS_R, GOAL_N), 
    append(HYPS_L, HYPS_R, HYPS)
  ) ;
  (HYPS = [HYP], GOAL_N = GOAL).

para_cla_b(HYP, GOAL, HGS) :- 
  (
    \+ imp_hyp(HYP),
    bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R)
  ) -> 
  (
    para_cla_b(HYP_L, GOAL_L, HGS_L),
    para_cla_b(HYP_R, GOAL_R, HGS_R),
    append(HGS_L, HGS_R, HGS)
  ) ;
  HGS = [([HYP], GOAL)].

para_cla_two((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  (imp_hyp(HYP_A) ; imp_hyp(HYP_B)),
  (
    abp(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ;
    abp(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) 
  ).

para_cla_many((HYP_A, HYP_B, GOAL), HYPS, HGS) :- 
  \+ imp_hyp(HYP_A),
  \+ imp_hyp(HYP_B),
  (
    type_hyp(a, HYP_A),
    para_cla_a(HYP_A, GOAL, HYPS, GOAL_T), 
    para_cla_b(HYP_B, GOAL_T, HGS)
  ;
    type_hyp(a, HYP_B),
    para_cla_a(HYP_B, GOAL, HYPS, GOAL_T), 
    para_cla_b(HYP_A, GOAL_T, HGS)
  ).

para_cla(H2G) :- 
  para_zero(H2G) -> true ;
  para_one(H2G, H2G_N) -> para_cla(H2G_N) ;
  para_cla_two(H2G, H2G_L, H2G_R) -> para_cla(H2G_L), !, para_cla(H2G_R) ;
  para_cla_many(H2G, HS, HGS) -> para_cla_aux(HS, HGS).

para_cla_aux(_, []).

para_cla_aux(HYPS, [([HYP], GOAL) | HGS]) :- 
  pluck(HYPS, CMP, REST), 
  para_cla((HYP, CMP, GOAL)), !,
  para_cla_aux(REST, HGS).