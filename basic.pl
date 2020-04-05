:- op(1200,  fy, +).   % Positive formula
:- op(1200,  fy, -).   % Negative formula
:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
:- op(1130, xfy, <~>).  % negated equivalence
:- op(1110, xfy, <=).   % implication
:- op(1100, yfx, '|').  % disjunction
:- op(1100, yfx, '~|'). % negated disjunction
:- op(1000, yfx, &).    % conjunction
:- op(1000, yfx, ~&).   % negated conjunction
:- op(500,   fy, ~).    % negation
:- op(500,  xfy, :).
:- op(499,   fy, !).     % universal quantifier
:- op(499,   fy, ?).     % existential quantifier
:- op(499,  xfy, =).
:- op(499,  xfy, \=).

%%%%%%%%%%%%%%%% GENERIC %%%%%%%%%%%%%%%% 
  
syneq(X, Y) :- X == Y.

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

% logical(SYMB) :- 
%    member(SYMB, ['!', '?', '~', '|', '&', '=>', '<=>', '=', '+', '-', '@', '#', 'false', 'true']).
% 
% nlss(TERM, NLSS) :- 
%   sub_term(NLSS, TERM),
%   atom(NLSS), 
%   \+ logical(NLSS).
% 
% nlsss(TERM, NLSSS) :- 
%   findall(NLSS, nlss(TERM, NLSS), NLSSS).

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
fof(_, _, _, _, _).
cnf(_, _, _).
cnf(_, _, _, _).
cnf(_, _, _, _, _).

hyp_sf((_, SF), SF).

incr_ov_term(_, VAR, _) :- var(VAR), !, false.
incr_ov_term(NUM, #(NUM_I), #(NUM_O)) :- !,
  NUM_I < NUM -> NUM_O = NUM_I ; 
  NUM_O is NUM_I + 1.
incr_ov_term(_, @(NUM), @(NUM)) :- !.
incr_ov_term(NUM, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(incr_ov_term(NUM), TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

safe_subst_term(_, _, VAR, _) :- var(VAR), !, false.
safe_subst_term(CNT, TERM_S, #(NUM), TERM_O) :- !, 
  CNT = NUM -> TERM_O = TERM_S 
; 
  CNT < NUM -> 
  num_pred(NUM, PRED), 
  TERM_O = #(PRED) 
; 
  TERM_O = #(NUM).

safe_subst_term(_, _, @(NUM), @(NUM)) :- !.
safe_subst_term(NUM, TERM_S, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I], 
  maplist_cut(safe_subst_term(NUM, TERM_S), TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O]. 

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

safe_subst_form(_, _, FORM, FORM) :- log_const(FORM), !.

safe_subst_form(NUM, TERM, ~ FORM_I, ~ FORM_O) :- !,
  safe_subst_form(NUM, TERM, FORM_I, FORM_O).

safe_subst_form(NUM, TERM, FORM_I, FORM_O) :-
  FORM_I =.. [QTF, SUB_I], 
  qtf(QTF), !, 
  SUCC is NUM + 1,
  incr_ov_term(0, TERM, TERM_N),
  safe_subst_form(SUCC, TERM_N, SUB_I, SUB_O), 
  FORM_O =.. [QTF, SUB_O]. 

safe_subst_form(NUM, TERM, FORM_I, FORM_O) :- 
  FORM_I =.. [BCT, FORM_IA, FORM_IB], 
  bct(BCT), !, 
  safe_subst_form(NUM, TERM, FORM_IA, FORM_OA),
  safe_subst_form(NUM, TERM, FORM_IB, FORM_OB),
  FORM_O =.. [BCT, FORM_OA, FORM_OB]. 

safe_subst_form(NUM, TERM, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I], 
  maplist_cut(safe_subst_term(NUM, TERM), TERMS_I, TERMS_O), 
  FORM_O =.. [REL | TERMS_O]. 

safe_subst_form(TERM, FORM, FORM_N) :- 
  safe_subst_form(0, TERM, FORM, FORM_N).

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
  (a(PID, DIR, x(FI), PRF), FP, FI), 
  (x(FI), SF_N), 
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  ab(DIR, SF, SF_N), !.

bp(
  (PID, SF), 
  (b(PID, x(FI), PRF_A, PRF_B), FP, FI), 
  (x(FI), SF_L),
  (x(FI), SF_R),
  (PRF_A, FP, FI_N),
  (PRF_B, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  bb(SF, SF_L, SF_R), !.

cp(
  (PID, SF), 
  TERM, 
  (c(PID, TERM, x(FI), PRF), FP, FI), 
  (x(FI), SF_N),
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1, 
  cb(TERM, SF, SF_N), !.

dp(
  (PID, SF),
  (d(PID, x(FI), PRF), FP, FI), 
  (x(FI), SF_N),
  (PRF, FP_N, FI_N)
) :-
  FP_N is FP + 1, 
  FI_N is FI + 1, 
  db(FP, SF, SF_N), !.

fp(
  FORM,
  (f(FORM, x(FI), PRF_A, PRF_B), FP, FI), 
  (x(FI), (- FORM)),
  (x(FI), (+ FORM)),
  (PRF_A, FP, FI_N), 
  (PRF_B, FP, FI_N)
) :-
  FI_N is FI + 1, !.

tp(
  SF,
  JST,
  (t(SF, JST, x(FI), PRF), FP, FI),
  (x(FI), SF),
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1, !.

sp(
  (PID, SF),
  (s(PID, x(FI), PRF), FP, FI), 
  (x(FI), SF_N),
  (PRF, FP, FI_N)
) :- 
  FI_N is FI + 1,
  sb(SF, SF_N), !.

wp(
  (PID, _),
  (w(PID, PRF), FP, FI), 
  (PRF, FP, FI)
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

justified(CTX, + FORM, [aoc, SKM]) :- 
  \+ sub_term(@(_), FORM), 
  \+ sub_term(SKM, CTX), 
  inst_with_pars(0, FORM, CNT, (? ANTE) => CONS), 
  \+ sub_term(SKM, ANTE), 
  mk_skm_term(SKM, CNT, SKM_TERM),
  subst_form(SKM_TERM, ANTE, ANTE_N),
  ANTE_N == CONS.

justified(CTX, + FORM, [def, REL]) :- 
  \+ sub_term(REL, CTX), 
  strip_fas(FORM, NUM, ATOM <=> BODY), 
  \+ sub_term(REL, BODY), 
  mk_def_atom(REL, NUM, ATOM).



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

abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) :- 
  bp(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  ap(HYP_A, l, GOAL_TL, HYP_AL, GOAL_L),
  ap(HYP_A, r, GOAL_TR, HYP_AR, GOAL_R).

abpr(HYP_A, HYP_B, GOAL, HYP_AR, HYP_BL, GOAL_L, HYP_AL, HYP_BR, GOAL_R) :- 
  bp(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_TL, GOAL_TR), 
  ap(HYP_A, r, GOAL_TL, HYP_AR, GOAL_L),
  ap(HYP_A, l, GOAL_TR, HYP_AL, GOAL_R).

fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R) :- 
  hyp_sf(HYP, SF), 
  bb(SF, SF_L, _),
  fps(SF_L, GOAL, HYP_LN, HYP_L, GOAL_LN, GOAL_L), 
  bp(HYP, GOAL_LN, HYP_LP, HYP_R, GOAL_LPN, GOAL_R), 
  mate(HYP_LP, HYP_LN, GOAL_LPN).

fbpr(HYP, GOAL, HYP_L, HYP_RN, HYP_R, GOAL_L, GOAL_R) :- 
  hyp_sf(HYP, SF), 
  bb(SF, _, SF_R),
  fps(SF_R, GOAL, HYP_RN, HYP_R, GOAL_RN, GOAL_R), 
  bp(HYP, GOAL_RN, HYP_L, HYP_RP, GOAL_L, GOAL_RPN), 
  mate(HYP_RP, HYP_RN, GOAL_RPN).

fps(+ FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

fps(- FORM, GOAL, HYP_P, HYP_N, GOAL_P, GOAL_N) :- 
  fp(FORM, GOAL, HYP_N, HYP_P, GOAL_N, GOAL_P).

cdp(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  GOAL = (_, FP, _), 
  dp(HYP_D, GOAL, HYP_N_D, GOAL_T), 
  cp(HYP_C, @(FP), GOAL_T, HYP_N_C, GOAL_N). 

dp_lax(CNT_I, HYP_I, GOAL_I, CNT_O, HYP_O, GOAL_O) :-  
  dp(HYP_I, GOAL_I, HYP_T, GOAL_T) -> 
  ( 
    vac_qtf(HYP_I) -> CNT_T = CNT_I ;
    CNT_T is CNT_I + 1
  ),
  dp_lax(CNT_T, HYP_T, GOAL_T, CNT_O, HYP_O, GOAL_O) 
;
  CNT_O = CNT_I, 
  HYP_O = HYP_I, 
  GOAL_O = GOAL_I. 
  
cp_lax(CNT, HYP_I, GOAL_I, HYP_O, GOAL_O) :-  
  vac_qtf(HYP_I) ->  
  (
    cp(HYP_I, _, GOAL_I, HYP_T, GOAL_T) -> 
    cp_lax(CNT, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  )
;
  (
    num_pred(CNT, PRED) -> 
    cp(HYP_I, _, GOAL_I, HYP_T, GOAL_T),
    cp_lax(PRED, HYP_T, GOAL_T, HYP_O, GOAL_O)  
  ;
    HYP_O = HYP_I, 
    GOAL_O = GOAL_I
  ).

cdp_lax(HYP_C, HYP_D, GOAL, HYP_N_C, HYP_N_D, GOAL_N) :- 
  type_hyp(d, HYP_D),
  type_hyp(c, HYP_C),
  dp_lax(0, HYP_D, GOAL, CNT, HYP_N_D, GOAL_T), 
  cp_lax(CNT, HYP_C, GOAL_T, HYP_N_C, GOAL_N). 
  
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

cf_lits(CLA_L | CLA_R, LITS) :- !, 
  cf_lits(CLA_L, LITS_L), 
  cf_lits(CLA_R, LITS_R), 
  append(LITS_L, LITS_R, LITS).
  
cf_lits(LIT, [LIT]). 

cf_atoms(CF, ATOMS) :- 
  cf_lits(CF, LITS),
  maplist_cut(lit_atom, LITS, ATOMS). 

lit_atom(LIT, ATOM) :- 
  LIT = (~ ATOM) -> true ;
  LIT = ATOM.

close_lvs(BODY, FORM) :- 
  term_variables(BODY, VARS), 
  bind_vars(0, VARS),
  length(VARS, NUM), 
  add_fas(NUM, BODY, FORM).

close_ovs(BODY, FORM) :- 
  ov_bound(BODY, NUM),
  add_fas(NUM, BODY, FORM).

trunc_pred(NUM, PRED) :- 
  0 < NUM -> PRED is NUM - 1 ; 
  PRED = 0.

uct_break(~ FORM, '~', FORM).
uct_break(FORM, QTF, SUB) :- 
  qtf_break(FORM, QTF, SUB).

qtf_break(FORM, QTF, SUB) :- 
  FORM =.. [QTF, SUB],
  qtf(QTF).

bct_break(FORM, BCT, FORM_A, FORM_B) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT).

max(NUM_A, NUM_B, MAX) :-
  NUM_A < NUM_B -> MAX = NUM_B ; 
  MAX = NUM_A.

num_succ(NUM, SUCC) :-
  SUCC is NUM + 1.

positive(NUM) :- 0 < NUM.

ovs(~ FORM, OVS) :- !, ovs(FORM, OVS).
ovs(FORM, OVS) :- 
  qtf_break(FORM, _, SUB), !, 
  ovs(SUB, TEMP),
  include(positive, TEMP, FILT), 
  maplist(num_pred, FILT, OVS).
ovs(FORM, OVS) :- 
  bct_break(FORM, _, FORM_A, FORM_B), !, 
  ovs(FORM_A, BND_A),
  ovs(FORM_B, BND_B),
  union(BND_A, BND_B, OVS).
ovs(FORM, OVS) :- 
  findall(NUM, sub_term(#(NUM), FORM), OVS). 
  
ov_bound(~ FORM, BND) :- !, ov_bound(FORM, BND).
ov_bound(FORM, BND) :- 
  qtf_break(FORM, _, SUB), !, 
  ov_bound(SUB, TEMP),
  trunc_pred(TEMP, BND).
ov_bound(FORM, BND) :- 
  bct_break(FORM, _, FORM_A, FORM_B), !, 
  ov_bound(FORM_A, BND_A),
  ov_bound(FORM_B, BND_B),
  max(BND_A, BND_B, BND).
ov_bound(FORM, BND) :- 
  findall(NUM, sub_term(#(NUM), FORM), NUMS), 
  maplist(num_succ, NUMS, SUCCS), 
  max_list([0 | SUCCS], BND).
  
  

  

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

maplist_opt(_, [], []).
maplist_opt(GOAL, [ELEM_I | LIST_I], LIST_O) :- 
  call(GOAL, ELEM_I, RST), !, 
  (
    RST = some(ELEM_O) -> 
    maplist_opt(GOAL, LIST_I, LIST_T), 
    LIST_O = [ELEM_O | LIST_T] 
  ; 
    RST = none, 
    maplist_opt(GOAL, LIST_I, LIST_O)
  ).

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

bind_vars(_, []).
bind_vars(NUM, [#(NUM) | VARS]) :- 
  SUCC is NUM + 1,
  bind_vars(SUCC, VARS).

mk_skm_term(SKM, NUM, SKM_TERM) :-
  mk_pars(NUM, PARS), 
  SKM_TERM =.. [SKM | PARS].

mk_def_atom(REL, NUM, ATOM) :-
  mk_vars(NUM, TEMP),
  reverse(TEMP, VARS),
  ATOM =.. [REL | VARS].

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

mk_mono(0, Cons, Cons).

mk_mono(NUM, Cons, ! ! ((#(1) = #(0)) => MONO)) :-
  num_pred(NUM, Pred), 
  mk_mono(Pred, Cons, MONO), !.

term_funaris(VAR, _) :- var(VAR), !, false.
term_funaris(#(_), []) :- !.
term_funaris(@(_), []) :- !.
term_funaris(TERM, FAS) :- 
  TERM =.. [FUN | TERMS], 
  length(TERMS, LTH),
  maplist_cut(term_funaris, TERMS, FASS), 
  union([[(FUN, LTH)] | FASS], FAS).

form_funaris(FORM, []) :- log_const(FORM), !.
form_funaris(~ FORM, FUNS) :- !, form_funaris(FORM, FUNS).
form_funaris(FORM, FUNS) :- 
  FORM =.. [UCT, SUB], 
  uct(UCT), !, 
  form_funaris(SUB, FUNS).
form_funaris(FORM, FUNS) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !, 
  form_funaris(FORM_A, FUNS_A),
  form_funaris(FORM_B, FUNS_B),
  union(FUNS_A, FUNS_B, FUNS).
form_funaris(FORM, FUNS) :-
  FORM =.. [_ | TERMS], 
  maplist_cut(term_funaris, TERMS, FUNSS),
  union(FUNSS, FUNS).

sf_funaris(SF, FUNS) :-
  sf_form(SF, FORM),
  form_funaris(FORM, FUNS).

sf_inv(+ FORM, - FORM).
sf_inv(- FORM, + FORM).

epmt(PREM, CONC, GOAL) :- 
  many_nb([d], [CONC], GOAL, [HYP_A], GOAL_A), 
  many_nb([c], [PREM], GOAL_A, [HYP_B], GOAL_B), 
  parac((HYP_B, HYP_A, GOAL_B)).
  
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
  
% fid_hyp(CTX, FIDs, FID, (OS, SF)) :- 
%   nth0(OS, FIDs, FID),
%   nth0(OS, CTX, SF).

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
    STRS = [] 
  ;
    STRS = [STR | REST],
    stream_strings(STRM, REST)
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

first_char(STR, CHAR) :- 
  string_codes(STR, [CODE | _]), 
  char_code(CHAR, CODE).

trim_ops(Src, Tgt) :- 
  read_line_to_string(Src, LINE), 
  (
    LINE = end_of_file -> true 
  ; 
    (
      first_char(LINE, '%') ;
      first_char(LINE, '#') ;
      first_char(LINE, '\n') 
    ) -> trim_ops(Src, Tgt) 
  ;
    re_replace("!="/g, "\\=", LINE, LINE0), 
    re_replace("~~~"/g, "~ ~ ~", LINE0, LINE1), 
    % re_replace("~\\?"/g, "~ ?", LINE0, LINE1), 
    % re_replace("~\\!"/g, "~ !", LINE1, LINE2), 
    re_replace("(~|&|=>|<=>|:)(~|\\!|\\?)"/g, "$1 $2", LINE1, LINE_F),
    write(Tgt, LINE_F), 
    write(Tgt, "\n"), 
    trim_ops(Src, Tgt)
  ).

no_bv_term(_, VAR) :- var(VAR), !.
no_bv_term(CNT, #(NUM)) :- !, NUM \= CNT.
no_bv_term(_, @(_)) :- !.
no_bv_term(CNT, TERM) :- 
  TERM =.. [_ | TERMS],
  maplist_cut(no_bv_term(CNT), TERMS).

no_bv_form(_, $true).
no_bv_form(_, $false). 
no_bv_form(NUM, ~ FORM) :- !, 
  no_bv_form(NUM, FORM). 
no_bv_form(NUM, FORM) :- 
  FORM =.. [QTF, SUB], 
  qtf(QTF), !,
  SUCC is NUM + 1,
  no_bv_form(SUCC, SUB).
no_bv_form(NUM, FORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !,
  no_bv_form(NUM, FORM_A),
  no_bv_form(NUM, FORM_B).
no_bv_form(NUM, FORM) :- 
  FORM =.. [_ | TERMS],
  maplist_cut(no_bv_term(NUM), TERMS).

vac_qtf(HYP) :- 
  hyp_form(HYP, FORM),
  FORM =.. [QTF, SUB], 
  qtf(QTF),
  no_bv_form(0, SUB).

fv_inc_term(_, VAR) :- var(VAR), !, false.
fv_inc_term(CNT, #(NUM), #(NEW)) :- !,
  NUM < CNT -> 
  NEW = NUM ;
  NEW is NUM + 1.
fv_inc_term(_, @(NUM), @(NUM)) :- !.
fv_inc_term(CNT, TERM_I, TERM_O) :- 
  TERM_I =.. [FUN | TERMS_I],
  maplist_cut(fv_inc_term(CNT), TERMS_I, TERMS_O), 
  TERM_O =.. [FUN | TERMS_O].

fv_inc_form(_, FORM, FORM) :- log_const(FORM), !.
fv_inc_form(NUM, ~ FORM_I, ~ FORM_O) :- !, 
  fv_inc_form(NUM, FORM_I, FORM_O). 
fv_inc_form(NUM, FORM_I, FORM_O) :- 
  FORM_I =.. [QTF, SUB_I], 
  qtf(QTF), !,
  SUCC is NUM + 1,
  fv_inc_form(SUCC, SUB_I, SUB_O), 
  FORM_O =.. [QTF, SUB_O]. 
fv_inc_form(NUM, FORM_I, FORM_O) :- 
  FORM_I =.. [BCT, FORM_IA, FORM_IB],
  bct(BCT), !,
  fv_inc_form(NUM, FORM_IA, FORM_OA),
  fv_inc_form(NUM, FORM_IB, FORM_OB), 
  FORM_O =.. [BCT, FORM_OA, FORM_OB].
fv_inc_form(NUM, FORM_I, FORM_O) :- 
  FORM_I =.. [REL | TERMS_I],
  maplist_cut(fv_inc_term(NUM), TERMS_I, TERMS_O),
  FORM_O =.. [REL | TERMS_O].

no_fv_term(_, VAR) :- var(VAR), !, false.
no_fv_term(CNT, #(NUM)) :- !, NUM < CNT.
no_fv_term(_, @(_)) :- !.
no_fv_term(CNT, TERM) :- 
  TERM =.. [_ | TERMS],
  maplist_cut(no_fv_term(CNT), TERMS).

no_fv_form(_, FORM) :- log_const(FORM), !.
no_fv_form(NUM, ~ FORM) :- !, 
  no_fv_form(NUM, FORM). 
no_fv_form(NUM, FORM) :- 
  FORM =.. [QTF, SUB], 
  qtf(QTF), !,
  SUCC is NUM + 1,
  no_fv_form(SUCC, SUB).
no_fv_form(NUM, FORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !,
  no_fv_form(NUM, FORM_A),
  no_fv_form(NUM, FORM_B).
no_fv_form(NUM, FORM) :- 
  FORM =.. [_ | TERMS],
  maplist_cut(no_fv_term(NUM), TERMS).

no_fv_sf(CNT, SF) :- 
  sf_form(SF, FORM),
  no_fv_form(CNT, FORM).

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

upnf_bct(BCT, ! FORM_A, FORM_B, ! NORM) :- 
  fv_inc_form(0, FORM_B, FORM_N), 
  upnf_bct(BCT, FORM_A, FORM_N, NORM).
upnf_bct(BCT, FORM_A, ! FORM_B, ! NORM) :- 
  fv_inc_form(0, FORM_A, FORM_N), 
  upnf_bct(BCT, FORM_N, FORM_B, NORM).
upnf_bct(BCT, FORM_A, FORM_B, NORM) :- 
  FORM_A \= (! _),
  FORM_B \= (! _),
  NORM =.. [BCT, FORM_A, FORM_B].
  
% upnf_not(! FORM, ? NORM) :- !, upnf_not(FORM, NORM).
% upnf_not(? FORM, ! NORM) :- !, upnf_not(FORM, NORM).
% upnf_not(FORM, ~ FORM). 

% upnf(FORM, FORM) :- log_const(FORM), !.
% upnf(~ FORM, NORM) :- !, 
%   upnf(FORM, TEMP), 
%   upnf_not(TEMP, NORM).
upnf(FORM, NORM)  :- 
  FORM =.. [BCT, FORM_A, FORM_B],
  bct(BCT), !, 
  upnf(FORM_A, NORM_A), 
  upnf(FORM_B, NORM_B), 
  upnf_bct(BCT, NORM_A, NORM_B, NORM).
upnf(! FORM, ! NORM) :- !, 
  upnf(FORM, NORM).
upnf(FORM, FORM). 

has_exists(? _).
has_exists(! FORM) :- has_exists(FORM).
has_exists(FORM_A & FORM_B) :- has_exists(FORM_A) ; has_exists(FORM_B).
has_exists(FORM_A | FORM_B) :- has_exists(FORM_A) ; has_exists(FORM_B).

has_qtf(! _).
has_qtf(? _).
has_qtf(~ FORM) :- has_qtf(FORM).
has_qtf(FORM) :- 
  FORM =.. [BCT, FORM_A, FORM_B], 
  bct(BCT), 
  (has_qtf(FORM_A) ; has_qtf(FORM_B)).

app_qtfs([], FORM, FORM).
app_qtfs([QTF | QTFS], FORM_I, FORM_O) :- 
  TEMP =.. [QTF, FORM_I],
  app_qtfs(QTFS, TEMP, FORM_O).

fnnf(QTFS, FORM_A & FORM_B, NORM) :- !, 
  fnnf([], FORM_A, NORM_A), 
  fnnf([], FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A & NORM_B, NORM).
fnnf(QTFS, FORM_A | FORM_B, NORM) :- !, 
  fnnf([], FORM_A, NORM_A), 
  fnnf([], FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A | NORM_B, NORM).
fnnf(QTFS, FORM_A => FORM_B, NORM) :- !, 
  fnnf([], ~ FORM_A, NORM_A), 
  fnnf([], FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A | NORM_B, NORM).

fnnf(QTFS, FORM_A <=> FORM_B, NORM) :- !, 
  has_qtf(FORM_A <=> FORM_B) ->
  fnnf(QTFS, FORM_A => FORM_B, NORM_A), 
  fnnf(QTFS, FORM_B => FORM_A, NORM_B),
  NORM = (NORM_A & NORM_B)
;
  fnnf([], FORM_A => FORM_B, NORM_A), 
  fnnf([], FORM_B => FORM_A, NORM_B),
  app_qtfs(QTFS, NORM_A & NORM_B, NORM).

fnnf(QTFS, ! FORM, NORM) :- !, fnnf(['!' | QTFS], FORM, NORM).
fnnf(QTFS, ? FORM, NORM) :- !, fnnf(['?' | QTFS], FORM, NORM).

fnnf(QTFS, ~ ~ FORM, NORM) :- !, fnnf(QTFS, FORM, NORM).

fnnf(QTFS, ~ (FORM_A & FORM_B), NORM) :- !, 
  fnnf([], ~ FORM_A, NORM_A), 
  fnnf([], ~ FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A | NORM_B, NORM).

fnnf(QTFS, ~ (FORM_A | FORM_B), NORM) :- !, 
  fnnf([], ~ FORM_A, NORM_A), 
  fnnf([], ~ FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A & NORM_B, NORM).

fnnf(QTFS, ~ (FORM_A => FORM_B), NORM) :- !, 
  fnnf([], FORM_A, NORM_A), 
  fnnf([], ~ FORM_B, NORM_B),
  app_qtfs(QTFS, NORM_A & NORM_B, NORM).

fnnf(QTFS, ~ (FORM_A <=> FORM_B), NORM) :- !, 
  fnnf([], (~ FORM_A | ~ FORM_B), NORM_A), 
  fnnf([], (FORM_A | FORM_B), NORM_B),
  app_qtfs(QTFS, NORM_A & NORM_B, NORM).

fnnf(QTFS, ~ (! FORM), NORM) :- !, fnnf(['?' | QTFS], ~ FORM, NORM).
fnnf(QTFS, ~ (? FORM), NORM) :- !, fnnf(['!' | QTFS], ~ FORM, NORM).

fnnf(QTFS, FORM, NORM) :- app_qtfs(QTFS, FORM, NORM).

distribute(! FORM, ! NORM) :- 
  distribute(FORM, NORM).

distribute(FORM_A & FORM_B, NORM_A & NORM_B) :- !, 
  distribute(FORM_A, NORM_A),
  distribute(FORM_B, NORM_B).

distribute(FORM_A | FORM_B, NORM) :- !, 
  distribute(FORM_A, TEMP_A),  
  distribute(FORM_B, TEMP_B),
  (
    TEMP_A = (FORM_L & FORM_R) -> 
    distribute((FORM_L | TEMP_B), CONJ_L), 
    distribute((FORM_R | TEMP_B), CONJ_R), 
    NORM = (CONJ_L & CONJ_R)
  ;
    TEMP_B = (FORM_L & FORM_R) -> 
    distribute((FORM_L | TEMP_A), CONJ_L), 
    distribute((FORM_R | TEMP_A), CONJ_R), 
    NORM = (CONJ_L & CONJ_R) 
  ;
    NORM = (TEMP_A | TEMP_B)
  ).  

% distribute(FORM_A | (FORM_B & FORM_C), NORM_L & NORM_R) :- !, 
%   distribute(FORM_B | FORM_A, NORM_L),  
%   distribute(FORM_C | FORM_A, NORM_R).  
% 
% distribute((FORM_A & FORM_B) | FORM_C, NORM_L & NORM_R) :- !, 
%   distribute(FORM_A | FORM_C, NORM_L),  
%   distribute(FORM_B | FORM_C, NORM_R).  

distribute(FORM, FORM).

trim_read(FILE, TERMS) :- 
  open(FILE, read, SRC), 
  atomic_concat(FILE, ".temp", TEMP),
  open(TEMP, write, TGT), 
  trim_ops(SRC, TGT), 
  close(SRC),
  close(TGT),
  atomic_concat("cat ", TEMP, CMD),
  shell(CMD),
  read_file_to_terms(TEMP, TERMS, []),
  delete_file(TEMP).

trim_consult(FILE) :- 
  dynamic(cnf/3),
  dynamic(cnf/4),
  dynamic(cnf/5),
  dynamic(fof/3),
  dynamic(fof/4),
  dynamic(fof/5),
  retractall(cnf(_, _, _)),
  retractall(cnf(_, _, _, _)),
  retractall(cnf(_, _, _, _, _)),
  retractall(fof(_, _, _)),
  retractall(fof(_, _, _, _)),
  retractall(fof(_, _, _, _, _)),
  open(FILE, read, SRC), 
  atomic_concat(FILE, ".temp", TEMP),
  open(TEMP, write, TGT), 
  trim_ops(SRC, TGT), 
  close(SRC),
  close(TGT),
  % atomic_concat("cat ", TEMP, CMD),
  % shell(CMD),
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
    cnf(ID, TYPE, TF), LNG = cnf ;
    fof(ID, TYPE, TF), LNG = fof 
  ),
  tf_form(LNG, TF, FORM),
  add_sign(TYPE, FORM, SF).

add_hyp((ID, SF), PROB_IN, PROB_OUT) :- 
  put_assoc(ID, PROB_IN, SF, PROB_OUT).

pose(TPTP, IDS, PROB) :- 
  trim_consult(TPTP),
  empty_assoc(EMP), 
  findall(HYP, hypothesis(HYP), HYPS), 
  maplist_cut(fst, HYPS, IDS),
  foldl(add_hyp, HYPS, EMP, PROB).

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
 
% nums_id([NUM], NUM) :- !.
% nums_id([NUM | NUMS], l(NUM, ID)) :- 
%   nums_id(NUMS, ID).
% 
% id_nums(l(NUM, ID), [NUM | LIST]) :- !, 
%   id_nums(ID, LIST).
% id_nums(NUM, [NUM]) :- number(NUM).

put_id(STRM, ID) :- 
  ID =.. [TYPE, NUM], !,
  put_char(STRM, TYPE),
  put_num(STRM, NUM).
put_id(STRM, ID) :- 
  atom(ID), 
  put_char(STRM, 'p'),
  put_atom(STRM, ID).
  
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

subst_fun_mul(OPEs, ONE, GOAL, NewOPEs) :-
  ONE = (_, (- (TERM_A = TERM_B))), 
  (
    TERM_A == TERM_B -> 
    (eq_refl(ONE, GOAL), NewOPEs = OPEs) ;
    subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs)
  ).

subst_fun_mul_0(OPEs, ONF, GOAL, OPEs) :- 
  ONF = (_, (- (TERM_A = TERM_B))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_mul_0(OPEs, ONE, GOAL, NewOPEs) :-
  break_eq_fun(OPEs, ONE, GOAL, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_mul_0(OPQEs, ONE, GOAL, NewOPQEs) :- 
  ONE = (_, (- (TERM_A0 = TERM_C))), 
  pluck_uniq(OPQEs, OPQE, REST),
  many_nb([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, (+ _ = _)),
  erient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, (+ TERM_A1 = TERM_B)),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_mul(REST, NewONE, GOAL1, NewOPQEs), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_fun_mul_aux(OPEs, [], OPEs).

subst_fun_mul_aux(OPEs, [(ONE, GOAL) | HGS], NewOPEs) :-
  subst_fun_mul(OPEs, ONE, GOAL, TempOPEs),
  subst_fun_mul_aux(TempOPEs, HGS, NewOPEs).

subst_rel_mul(HYP_L, OPEs, HYP_R, GOAL, NewOPEs) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  erient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(OPEs, OPA, ONA, GOAL_T, HGS),
  subst_fun_mul_aux(OPEs, HGS, NewOPEs). 

subst_fun_add(EQNS, (HYP, GOAL)) :-
  subst_fun_add(EQNS, HYP, GOAL).

subst_fun_add(EQNS, ONE, GOAL) :-
  ONE = (_, (- (TERM_A = TERM_B))), 
  (
    TERM_A == TERM_B -> 
    eq_refl(ONE, GOAL) ;
    subst_fun_add_0(EQNS, ONE, GOAL)
  ).

subst_fun_add_0(_, ONF, GOAL) :- 
  ONF = (_, (- (TERM_A = TERM_B))), 
  unify_with_occurs_check(TERM_A, TERM_B),
  eq_refl(ONF, GOAL).

subst_fun_add_0(EQNS, ONE, GOAL) :-
  break_eq_fun(EQNS, ONE, GOAL, HGS),
  maplist(subst_fun_add(EQNS), HGS). 

subst_fun_add_0(OPQEs, ONE, GOAL) :- 
  ONE = (_, (- (TERM_A0 = TERM_C))), 
  pluck_uniq(OPQEs, OPQE, REST),
  many_nb([c], [OPQE], GOAL, [PRE_OPE], GOAL_T), 
  PRE_OPE = (_, (+ _ = _)),
  erient_hyp(PRE_OPE, GOAL_T, OPE, GOAL0),
  OPE = (_, (+ TERM_A1 = TERM_B)),
  unify_with_occurs_check(TERM_A0, TERM_A1), 
  fp(TERM_B = TERM_C, GOAL0, NewONE, NewOPE, GOAL1, GOAL2), 
  subst_fun_add(REST, NewONE, GOAL1), 
  eq_trans(OPE, NewOPE, ONE, GOAL2).

subst_rel_add(EQNS, HYP_L, HYP_R, GOAL) :-  
  orient_sign(HYP_L, HYP_R, PreOPA, ONA),
  erient_hyp(PreOPA, GOAL, OPA, GOAL_T),
  break_eq_rel(EQNS, OPA, ONA, GOAL_T, HGS),
  maplist(subst_fun_add(EQNS), HGS).

 
erient_stom(SA, SA).
erient_stom(+ (TERM_A = TERM_B), + (TERM_B = TERM_A)).
erient_stom(- (TERM_A = TERM_B), - (TERM_B = TERM_A)).

erient_atom(ATOM, ATOM).
erient_atom(LHS = RHS, RHS = LHS).

unify_lit(~ ATOM_A, ~ ATOM_B) :- unify_atom(ATOM_A, ATOM_B).
unify_lit(ATOM_A, ATOM_B) :- unify_atom(ATOM_A, ATOM_B).

unify_atom(ATOM_A, ATOM_B) :- 
  erient_atom(ATOM_A, TEMP), 
  unify_with_occurs_check(TEMP, ATOM_B).

erient_form(FORM, FORM).
erient_form(LHS = RHS, RHS = LHS).

erient_lit(LIT, EQV) :- erient_form(LIT, EQV).
erient_lit(~ LHS = RHS, ~ RHS = LHS). 

erient_hyp(HYP, GOAL, HYP, GOAL).
erient_hyp(HYP_I, GOAL_I, HYP_O, GOAL_O) :- 
  HYP_I = (_, (+ (LHS = RHS))), 
  fp(RHS = LHS, GOAL_I, HYP_T, HYP_O, GOAL_T, GOAL_O), 
  eq_symm(HYP_I, HYP_T, GOAL_T), !. 

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

use_contra(HYP, GOAL) :- 
  use_lc(HYP, GOAL) ;
  (
    sp(HYP, GOAL, HYP_N, GOAL_N) ;
    ap(HYP, l, GOAL, HYP_N, GOAL_N) ; 
    ap(HYP, r, GOAL, HYP_N, GOAL_N) 
  ),
  use_contra(HYP_N, GOAL_N) ;
  bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  use_contra(HYP_L, GOAL_L),
  use_contra(HYP_R, GOAL_R).

lc(+ $false).
lc(- $true).
lt(+ $true).
lt(- $false).

bool_not($false, $true) :- !.
bool_not($true, $false) :- !.
bool_not(FORM, ~ FORM).

bool_or($true, _, $true) :- !.
bool_or(_, $true, $true) :- !.
bool_or($false, FORM, FORM) :- !.
bool_or(FORM, $false, FORM) :- !.
bool_or(FORM_L, FORM_R, FORM_L | FORM_R).

bool_and($false, _, $false) :- !.
bool_and(_, $false, $false) :- !.
bool_and($true, FORM, FORM) :- !.
bool_and(FORM, $true, FORM) :- !.
bool_and(FORM_L, FORM_R, FORM_L & FORM_R).

bool_norm(~ FORM, NORM) :- !, 
  bool_norm(FORM, TEMP), 
  bool_not(TEMP, NORM). 
 
bool_norm((FORM_L | FORM_R), NORM) :- !, 
  bool_norm(FORM_L, NORM_L), 
  bool_norm(FORM_R, NORM_R),
  bool_or(NORM_L, NORM_R, NORM).

bool_norm((FORM_L & FORM_R), NORM) :- !, 
  bool_norm(FORM_L, NORM_L), 
  bool_norm(FORM_R, NORM_R),
  bool_and(NORM_L, NORM_R, NORM).

bool_norm(FORM, FORM).

contra(+ FORM) :- bool_norm(FORM, $false).
contra(- FORM) :- bool_norm(FORM, $true).
tauto(+ FORM)  :- bool_norm(FORM, $true).
tauto(- FORM)  :- bool_norm(FORM, $false).

mate_nu(HYP0, HYP1, GOAL) :- 
  orient_sign(HYP0, HYP1, OPF, ONF),
  mate_pn_nu(OPF, ONF, GOAL).

mate(HYP0, HYP1, GOAL) :- 
  orient_sign(HYP0, HYP1, OPF, ONF),
  mate_pn(OPF, ONF, GOAL).
 
mate_pn(PYP, NYP, GOAL) :- 
  erient_hyp(PYP, GOAL, PYP_N, GOAL_N), 
  xp(PYP_N, NYP, GOAL_N).

mate_pn_nu(OPF, ONF, GOAL) :- 
  erient_hyp(OPF, GOAL, N_OPF, N_GOAL), 
  N_OPF = (_, (+ FORM_A)),
  ONF = (_, (- FORM_B)),
  unifiable(FORM_A, FORM_B, []), 
  xp(N_OPF, ONF, N_GOAL).

sf_sign_form(+ FORM, '+', FORM).
sf_sign_form(- FORM, '-', FORM).

connect_dsfs((DIR_A, SF_A), (DIR_B, SF_B)) :- 
  sf_sign_form(SF_A, SIGN_A, FORM_A),
  sf_sign_form(SF_B, SIGN_B, FORM_B),
  DIR_A \= DIR_B,
  SIGN_A \= SIGN_B,
  connect_forms(FORM_A, FORM_B).

connect_sfs(+ FORM_A, - FORM_B) :- 
  connect_forms(FORM_A, FORM_B).
  
connect_sfs(- FORM_A, + FORM_B) :- 
  connect_forms(FORM_A, FORM_B).

connect_forms(FORM_A, FORM_B) :- 
  unify_with_occurs_check(FORM_A, FORM_B).
  
connect_forms(TERM_A = TERM_B, FORM) :- 
  unify_with_occurs_check(TERM_B = TERM_A, FORM).



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
  use_contra(HYP, GOAL).
  
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
    member(CH, ['s', 't', 'x']) -> 
    get_num(STRM, NUM), 
    ID =.. [CH, NUM]
  ;
    CH = 'p' -> 
    get_atom(STRM, ID)
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

%%%%%%%%%%%%%%%% PROPOSITIONAL CONNECTION TABLEAUX %%%%%%%%%%%%%%%%

startable_hyp((_, SF)) :- 
  startable_sf(SF).

startable_sf(SF) :- 
  sb(SF, SF_N) -> startable_sf(SF_N) 
;
  aab(SF, SF_L, SF_R) -> 
  (startable_sf(SF_L) ; startable_sf(SF_R)) 
;
  bb(SF, SF_L, SF_R) -> 
  startable_sf(SF_L),
  startable_sf(SF_R)
; 
  lc(SF) 
; 
  SF = (+ _). 
  
path_redundant(HYP, PATH) :- 
  hyp_sf(HYP, SF),
  erient_stom(SF, SF_A),
  member((_, SF_B), PATH), 
  SF_A == SF_B.

pblx(PQ, HYPS, GOAL) :- 
  pluck(HYPS, HYP, REST), 
  pblx((start, PQ), REST, [], HYP, GOAL).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  sp(HYP, GOAL, HYP_N, GOAL_N), !, 
  pblx(MODE, HYPS, PATH, HYP_N, GOAL_N).
  
pblx((PHASE, q), HYPS, PATH, HYP, GOAL) :- 
  cp(HYP, _, GOAL, HYP_N, GOAL_N), !, 
  pblx((PHASE, q), HYPS, PATH, HYP_N, GOAL_N).

pblx(MODE, HYPS, PATH, HYP, GOAL) :- 
  aap(HYP, GOAL, HYP_L, HYP_R, GOAL_N), !, 
  (
    pblx(MODE, [HYP_R | HYPS], PATH, HYP_L, GOAL_N) ;
    pblx(MODE, [HYP_L | HYPS], PATH, HYP_R, GOAL_N)
  ).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  startable_hyp(HYP_R),
  pblx((start, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((match, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  (
    pblx((match, PQ), HYPS, PATH, HYP_L, GOAL_L),
    pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R)
  ;
    pblx((match, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R),
    pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L)
  ).
  
pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  fbpl(HYP, GOAL, HYP_L, HYP_R, HYP_LN, GOAL_L, GOAL_R), !, 
  pblx((block, PQ), HYPS, PATH, HYP_L, GOAL_L),
  pblx((block, PQ), [HYP_LN | HYPS], PATH, HYP_R, GOAL_R).

pblx((start, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((start, PQ), HYPS, PATH, HYP, GOAL) :-
  hyp_sf(HYP, (+ _)), 
  pblx((block, PQ), HYPS, PATH, HYP, GOAL).

pblx((match, _), _, [CMP | _], HYP, GOAL) :- 
  mate(HYP, CMP, GOAL).
  
pblx((block, _), _, _, HYP, GOAL) :-
  use_contra(HYP, GOAL).

pblx((block, _), _, PATH, HYP, GOAL) :- 
  member(CMP, PATH),
  mate(HYP, CMP, GOAL).

pblx((block, PQ), HYPS, PATH, HYP, GOAL) :- 
  \+ path_redundant(HYP, PATH),
  pluck(HYPS, HYP_N, REST), 
  pblx((match, PQ), REST, [HYP | PATH], HYP_N, GOAL). 
 



/*
iff_conv_0(HYP_A, HYP_B, GOAL) :- 
  bp(HYP_A, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  iff_conv_1(HYP_L, HYP_B, GOAL_L),
  iff_conv_1(HYP_R, HYP_B, GOAL_R).

iff_conv_1(HYP_A, HYP_B, GOAL) :- 
  bp(HYP_B, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R), 
  iff_conv_2(HYP_A, HYP_L, GOAL_L),
  iff_conv_2(HYP_A, HYP_R, GOAL_R).

iff_conv_2(HYP_A, HYP_B, GOAL) :- 
  ap(HYP_B, l, GOAL, HYP_N, GOAL_N), 
  mate(HYP_A, HYP_N, GOAL_N) ;
  ap(HYP_B, r, GOAL, HYP_N, GOAL_N), 
  mate(HYP_A, HYP_N, GOAL_N).

iff_conv(HYP_A, HYP_B, GOAL) :- 
  aap(HYP_B, GOAL, HYP_BL, HYP_BR, GOAL_T), 
  ap(HYP_P, l, GOAL, HYP_L, GOAL_L), 
  iff_conv_0(HYP_L, HYP_N, GOAL_L),
  ap(HYP_P, r, GOAL, HYP_R, GOAL_R), 
  iff_conv_0(HYP_R, HYP_N, GOAL_R).
*/

sign_flip('+', '-').
sign_flip('-', '+').

iff_sf_conv(SF_I, SF_O) :- 
  SF_I =.. [SIGN, (FORM_A <=> FORM_B)],
  sign_flip(SIGN, FLIP),
  SF_O =.. [FLIP, ((FORM_A | FORM_B) & (~ FORM_A | ~ FORM_B))].

iff_conv((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  hyp_sf(HYP_A, SF_A),
  iff_sf_conv(SF_A, SF_N), 
  fps(SF_N, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N),
  pblx(p, [HYP_A, HYP_T], GOAL_T).

e_iff_conv((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  hyp_sf(HYP_A, - (FORM_A <=> FORM_B)),
  FORM = ((~ FORM_A | ~ FORM_B) & (FORM_A | FORM_B)),
  fp(FORM, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N),
  pblx(p, [HYP_A, HYP_T], GOAL_T).

%%%%%%%%%%%%%%%% PARALLEL DECOMPOSITION PREDICATES %%%%%%%%%%%%%%%%
  
para_m((HYP_A, HYP_B, GOAL)) :- 
  mate(HYP_A, HYP_B, GOAL).

para_s((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  sp(HYP_A, GOAL, HYP_AN, GOAL_N). 
  
para_s((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  sp(HYP_B, GOAL, HYP_BN, GOAL_N). 
  
para_c((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_B, GOAL_N)) :- 
  cp(HYP_A, _, GOAL, HYP_NA, GOAL_N).

para_cd((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  cdp(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

para_ab((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
  abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

para(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> para(H2G_N) ;
  para_cd(H2G, H2G_N) -> para(H2G_N) ;
  para_ab(H2G, H2G_L, H2G_R) ->
  para(H2G_L), !, 
  para(H2G_R).



%%%%%%%%%%%%%%%% PARALLEL SWITCH DECOMPOSITION %%%%%%%%%%%%%%%%

paras_ab((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
  abpr(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ; 
  abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) ;
  abpr(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R).

paras(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> paras(H2G_N) ;
  para_cd(H2G, H2G_N) -> paras(H2G_N) ;
  paras_ab(H2G, H2G_L, H2G_R),
  paras(H2G_L),  
  paras(H2G_R).




%%%%%%%%%%%%%%%% PARALLEL TF DECOMPOSITION %%%%%%%%%%%%%%%%

paratf_zero((HYP, _, GOAL)) :- 
  use_contra(HYP, GOAL).

paratf_one((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  (
    bp(HYP_A, GOAL, HYP_T, HYP_N, GOAL_T, GOAL_N) ;
    bp(HYP_A, GOAL, HYP_N, HYP_T, GOAL_N, GOAL_T) 
  ),
  use_contra(HYP_T, GOAL_T).

paratf_one((HYP_A, HYP_B, GOAL), (HYP_N, HYP_B, GOAL_N)) :- 
  pluck([l, r], DIR, [FLP]), 
  hyp_sf(HYP_A, SF), 
  ab(DIR, SF, SF_T), 
  tauto(SF_T), 
  ap(HYP_A, FLP, GOAL, HYP_N, GOAL_N). 

paratf(H2G) :- 
  para_m(H2G) -> true ;
  paratf_zero(H2G) -> true ;
  para_s(H2G, H2G_N) -> paratf(H2G_N) ;
  para_cd(H2G, H2G_N) -> paratf(H2G_N) ;
  paratf_one(H2G, H2G_N) -> paratf(H2G_N) ;
  paras_ab(H2G, H2G_L, H2G_R),
  paratf(H2G_L),  
  paratf(H2G_R).





%%%%%%%%%%%%%%%% PARALLEL LAX DECOMPOSITION %%%%%%%%%%%%%%%%

% parav_cd((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
%   vac_qtf(HYP_A), 
%   (
%     cp(HYP_A, _, GOAL, HYP_AN, GOAL_N) ; 
%     dp(HYP_A, GOAL, HYP_AN, GOAL_N)
%   ).
% 
% parav_cd((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
%   vac_qtf(HYP_B), 
%   (
%     cp(HYP_B, _, GOAL, HYP_BN, GOAL_N) ; 
%     dp(HYP_B, GOAL, HYP_BN, GOAL_N)
%   ).

% paral_one((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
%   sp(HYP_A, GOAL, HYP_AN, GOAL_N). 
%   
% paral_one((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
%   sp(HYP_B, GOAL, HYP_BN, GOAL_N). 

paral_cd((HYP_A, HYP_B, GOAL), (HYP_NA, HYP_NB, GOAL_N)) :- 
  cdp_lax(HYP_A, HYP_B, GOAL, HYP_NA, HYP_NB, GOAL_N) ;
  cdp_lax(HYP_B, HYP_A, GOAL, HYP_NB, HYP_NA, GOAL_N).

paral(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> paral(H2G_N) ;
  % parav_cd(H2G, H2G_N) -> paral(H2G_N) ;
  paral_cd(H2G, H2G_N) -> paral(H2G_N) ;
  para_ab(H2G, H2G_L, H2G_R), !,
  paral(H2G_L), !, 
  paral(H2G_R).

parad(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> parad(H2G_N) ;
  % parav_cd(H2G, H2G_N) -> paral(H2G_N) ;
  para_cd(H2G, H2G_N) -> parad(H2G_N) ;
  para_ab(H2G, H2G_L, H2G_R), 
  parad(H2G_L), 
  parad(H2G_R)
;
  parad_a(H2G, H2G_N),
  parad(H2G_N).

%%%%%%%%%%%%%%%% NEGATION NORMALIZATION %%%%%%%%%%%%%%%%

a_para((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  ap(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  ap(HYP_A, r, GOAL, HYP_AN, GOAL_N).

parad_a((HYP_A, HYP_B, GOAL), (HYP_AN, HYP_B, GOAL_N)) :- 
  ap(HYP_A, l, GOAL, HYP_AN, GOAL_N) ;
  ap(HYP_A, r, GOAL, HYP_AN, GOAL_N).

parad_a((HYP_A, HYP_B, GOAL), (HYP_A, HYP_BN, GOAL_N)) :- 
  ap(HYP_B, l, GOAL, HYP_BN, GOAL_N) ;
  ap(HYP_B, r, GOAL, HYP_BN, GOAL_N).

%vppr(H2G) :- 
%  para_m(H2G) -> true ;
%  para_s(H2G, H2G_N) -> vppr(H2G_N) ;
%  paral_cd(H2G, H2G_N) -> vppr(H2G_N) ;
%  parad_a(H2G, H2G_N),
%  vppr(H2G_N) 
%;
%  para_ab(H2G, H2G_L, H2G_R),
%  vppr(H2G_L),  
%  vppr(H2G_R).

fnnf(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> fnnf(H2G_N) ;
  para_ab(H2G, H2G_L, H2G_R) -> fnnf(H2G_L), !, fnnf(H2G_R) ;
  para_cd(H2G, H2G_N) -> fnnf(H2G_N) ;
  H2G = (PREM, CONC, GOAL), 
  (
    type_hyp(c, PREM),
    bp(CONC, GOAL, CONC_L, CONC_R, GOAL_L, GOAL_R), 
    fnnf((PREM, CONC_L, GOAL_L)),
    fnnf((PREM, CONC_R, GOAL_R))
  ;
    imp_hyp(PREM),
    parad_a(H2G, H2G_N),
    fnnf(H2G_N)
  ;  
    e_iff_conv(H2G, H2G_N), 
    fnnf(H2G_N)
  ).

  
vnnf(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> vnnf(H2G_N) ;
  para_cd(H2G, H2G_N) -> vnnf(H2G_N) ;
  parad_a(H2G, H2G_N),
  vnnf(H2G_N) 
;
  paras_ab(H2G, H2G_L, H2G_R),
  vnnf(H2G_L),  
  vnnf(H2G_R)
;
  iff_conv(H2G, H2G_N), 
  vnnf(H2G_N).

%%%%%%%%%%%%%%%% PARALLEL CLAUSAL DECOMPOSITION %%%%%%%%%%%%%%%%

imp_hyp(HYP) :- 
  hyp_form(HYP, FORM),
  member(FORM, [(_ => _), (_ <=> _)]).

parac_a_aux(HYP, GOAL, HYP_L, HYP_R, NEW_GOAL) :- 
  \+ imp_hyp(HYP), 
  ap(HYP, l, GOAL, HYP_L, TEMP_GOAL),
  ap(HYP, r, TEMP_GOAL, HYP_R, NEW_GOAL).

parac_a(HYP, GOAL, HYPS, GOAL_N) :- 
  parac_a_aux(HYP, GOAL, HYP_L, HYP_R, GOAL0) -> 
  (
    parac_a(HYP_L, GOAL0, HYPS_L, GOAL1),
    parac_a(HYP_R, GOAL1, HYPS_R, GOAL_N), 
    append(HYPS_L, HYPS_R, HYPS)
  ) ;
  (HYPS = [HYP], GOAL_N = GOAL).

parac_b(HYP, GOAL, HGS) :- 
  (
    \+ imp_hyp(HYP),
    bp(HYP, GOAL, HYP_L, HYP_R, GOAL_L, GOAL_R)
  ) -> 
  (
    parac_b(HYP_L, GOAL_L, HGS_L),
    parac_b(HYP_R, GOAL_R, HGS_R),
    append(HGS_L, HGS_R, HGS)
  ) ;
  HGS = [([HYP], GOAL)].

parac_two((HYP_A, HYP_B, GOAL), (HYP_AL, HYP_BL, GOAL_L), (HYP_AR, HYP_BR, GOAL_R)) :- 
  (imp_hyp(HYP_A) ; imp_hyp(HYP_B)),
  (
    abpl(HYP_A, HYP_B, GOAL, HYP_AL, HYP_BL, GOAL_L, HYP_AR, HYP_BR, GOAL_R) ;
    abpl(HYP_B, HYP_A, GOAL, HYP_BL, HYP_AL, GOAL_L, HYP_BR, HYP_AR, GOAL_R) 
  ).

parac_many((HYP_A, HYP_B, GOAL), HYPS, HGS) :- 
  \+ imp_hyp(HYP_A),
  \+ imp_hyp(HYP_B),
  (
    type_hyp(a, HYP_A),
    parac_a(HYP_A, GOAL, HYPS, GOAL_T), 
    parac_b(HYP_B, GOAL_T, HGS)
  ;
    type_hyp(a, HYP_B),
    parac_a(HYP_B, GOAL, HYPS, GOAL_T), 
    parac_b(HYP_A, GOAL_T, HGS)
  ).

parac(H2G) :- 
  para_m(H2G) -> true ;
  para_s(H2G, H2G_N) -> parac(H2G_N) ;
  para_cd(H2G, H2G_N) -> parac(H2G_N) ;
  parac_two(H2G, H2G_L, H2G_R) -> parac(H2G_L), !, parac(H2G_R) ;
  parac_many(H2G, HS, HGS) -> parac_aux(HS, HGS).

parac_aux(_, []).

parac_aux(HYPS, [([HYP], GOAL) | HGS]) :- 
  member(CMP, HYPS), 
  parac((HYP, CMP, GOAL)), !,
  parac_aux(HYPS, HGS).