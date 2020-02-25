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
:- op(950,  xfy, ^).    % function application
:- op(500,   fy, ~).    % negation
:- op(500,  xfy, :).
:- op(499,   fy, !).     % universal quantifier
:- op(499,   fy, ?).     % existential quantifier
:- op(499,  xfy, =).
:- op(499,  xfy, \=).

fof(_, _, _).
fof(_, _, _, _).
cnf(_, _, _).
cnf(_, _, _, _).

incr_idx(Depth, Idx, #(NewIdx)) :- 
  NewIdx is Idx + Depth.

% Requires : Term is variable-free
% NewForm = Form[0/Term]
subst(Term, Form, NewForm) :- 
  map_var_form(subst_aux(Term), 0, Form, NewForm).

subst_aux(Term, Num, Num, NewTerm) :- 
  map_var_term(incr_idx(Num), Term, NewTerm).

subst_aux(_, Tgt, Num, #(Num)) :-
  Num < Tgt.

subst_aux(_, Tgt, Num, #(Pred)) :- 
  Tgt < Num,
  Pred is Num - 1.

closed_form(Form) :- 
  map_var_form(closed_form_aux, 0, Form, _).

closed_form_aux(Depth, Idx, _) :-
  Idx < Depth.

ovar_free_term(Term) :- 
  map_var_term(alwyas_fail, Term, _).

alwyas_fail(_, _) :- false.

union([], []).

union([List | Lists], Set) :- 
  union(Lists, TempSet),
  union(List, TempSet, Set).

mark(Num) :-
  number_string(Num, NumStr),
  strings_concat(["Tracing ", NumStr, "\n"], Msg),
  write(Msg).

repeat(0, _).

repeat(Num, Goal) :- 
  0 < Num, 
  Pred is Num - 1, 
  call(Goal),
  repeat(Pred, Goal).

write_break(Num, Term) :-
  write(Term),
  repeat(Num, write("\n")).

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

where(Elem, [_ | List], Num) :- 
  where(Elem, List, Pred),
  Num is Pred + 1.

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

write_file(Target, Term) :-
  open(Target, write, Stream),
  write(Stream, Term),
  close(Stream).

pick(Goal, [Elem | Rem], Elem, Rem) :- 
  call(Goal, Elem), !.

pick(Goal, [ElemA | List], ElemB, [ElemA | Rem]) :- 
  pick(Goal, List, ElemB, Rem).

find(Goal, List, Elem) :- 
  pick(Goal, List, Elem, _).

pluck_uniq(List, Elem, Rest) :- 
  pluck_uniq([], List, Elem, Rest).

pluck_uniq(Acc, [Elem | List], Elem, Rest) :- 
  \+ member(Elem, Acc),
  append(Acc, List, Rest).

pluck_uniq(Acc, [Elem | List], Pick, Rest) :- 
  pluck_uniq([Elem | Acc], List, Pick, Rest).

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

first(Goal, [Elem | _], Result) :-
  call(Goal, Elem, Result), !.

first(Goal, [_ | List], Result) :-
  first(Goal, List, Result).

collect(_, [], []).

collect(Goal, [Elem | List], Results) :-
  call(Goal, Elem, Result) -> 
  ( collect(Goal, List, TempResults),
    Results = [Result | TempResults] ) ; 
  collect(Goal, List, Results).

any(Goal, [Elem | _]) :-
  call(Goal, Elem).

any(Goal, [_ | List]) :-
  any(Goal, List).

list_br_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with("\n\n", Strs, Str).
  
list_str(List, Str) :-
  maplist(term_string, List, Strs), 
  strings_concat_with(", ", Strs, Str).

last([Elem], Elem). 

last([_ | List], Elem) :- last(List, Elem). 

num_pred(Num, Pred) :-
  0 < Num,
  Pred is Num - 1.

unneg(~ Atom, Atom) :- !.
unneg(Atom, Atom).

write_file_punct(Filename, Term) :- 
  term_string(Term, TermStr),
  string_concat(TermStr, ".", Str),
  write_file(Filename, Str).

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

ucla(Lit) :-
  Lit \= (_ | _), 
  ulit(Lit).

uqla(! Form) :- 
  uqla(Form).

uqla(Form) :- 
  Form \= ! _, 
  ucla(Form).

sqla(+ Form) :- 
  uqla(Form).

sqla(- Form) :- 
  uqla(Form).

atom_tptp(TPTP) :- 
  \+ member(TPTP, 
    [ (! _ : _), (? _ : _), (~ _), 
      (_ | _), (_ & _), (_ => _), (_ <=> _) ]).

mono_body(0, Form, Form).

mono_body(Num, ! ! (#(1) = #(0) => Form), Cons) :- 
  num_pred(Num, Pred),
  mono_body(Pred, Form, Cons).

hyp_dfd(+ (Dfd <=> Form), Dfd) :- 
  \+ sub_term(Dfd, Form). 

break_fas(! FaVarsA : Form, FaVars, Body) :-
  break_fas(Form, FaVarsB, Body),
  append(FaVarsA, FaVarsB, FaVars), !.

break_fas(Body, [], Body) :-
  Body \= ! _. 

analyze_forall(! Form, Num, Body) :-
  analyze_forall(Form, Pred, Body),
  Num is Pred + 1. 

analyze_forall(Form, 0, Form).

mk_skolem_arg(FaNum, Arg) :- 
  num_pred(FaNum, Pred), 
  mk_skolem_arg(Pred, Temp), 
  append(Temp, [#(Pred)], Arg).

mk_skolem_arg(0, []).

count_fa(! Form, Num, Body) :-
  count_fa(Form, Pred, Body),
  Num is Pred + 1, !.

count_fa(Form, 0, Form).

count_ex(? Form, Num, Body) :-
  count_fa(Form, Pred, Body),
  Num is Pred + 1, !.

count_ex(Form, 0, Form).

break_aoc(Form, FaNum, ExNum, Ante, Cons) :-
  count_fa(Form, FaNum, Temp => Cons), 
  count_ex(Temp, ExNum, Ante). 

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

maplist_cut(Goal, [Elem | List]) :- 
  call(Goal, Elem), !, 
  maplist_cut(Goal, List). 

maplist_cut(_, []).

maplist_cut(Goal, [ElemA | ListA], [ElemB | ListB]) :- 
  call(Goal, ElemA, ElemB), !, 
  maplist_cut(Goal, ListA, ListB). 

maplist_cut(_, [], []).

maplist_cut(Goal, [ElemA | ListA], [ElemB | ListB], [ElemC | ListC]) :- 
  call(Goal, ElemA, ElemB, ElemC), !, 
  maplist_cut(Goal, ListA, ListB, ListC). 

maplist_cut(_, [], [], []).

maplist_idx(_, _, []).

maplist_idx(Goal, Num, [Elem | List]) :- 
  call(Goal, Num, Elem), 
  Succ is Num + 1,
  maplist_idx(Goal, Succ, List).

maplist_idx(_, _, [], []).

maplist_idx(Goal, Num, [ElemA | ListA], [ElemB | ListB]) :- 
  call(Goal, Num, ElemA, ElemB), 
  Succ is Num + 1,
  maplist_idx(Goal, Succ, ListA, ListB).


mk_vars(0, []).  

mk_vars(Num, [#(Pred) | Vars]) :- 
  num_pred(Num, Pred),
  mk_vars(Pred, Vars). 

mk_skm_term(Skm, Num, Skm ^ RevVars) :-
  mk_vars(Num, Vars), 
  reverse(Vars, RevVars).

mk_def_atom(Prd, Num, Atom) :-
  mk_vars(Num, Vars),
  Atom =.. [Prd | Vars].

/* Monotonicity */

mk_mono_args(0, [], []).

mk_mono_args(Num, [#(NumA) | VarsA], [#(NumB) | VarsB]) :-
  NumA is (Num * 2) - 1, 
  NumB is (Num * 2) - 2, 
  Pred is Num - 1,
  mk_mono_args(Pred, VarsA, VarsB).

mk_mono_eq(Num, Fun, (Fun ^ VarsA) = (Fun ^ VarsB)) :- 
  mk_mono_args(Num, VarsA, VarsB).

mk_mono_iff(Num, Rel, AtomA <=> AtomB) :- 
  mk_mono_args(Num, VarsA, VarsB),
  AtomA =.. [Rel | VarsA],
  AtomB =.. [Rel | VarsB], !.

mk_mono_fun(Num, Fun, Mono) :- 
  mk_mono_eq(Num, Fun, Eq), 
  mk_mono(Num, Eq, Mono), !.

mk_mono_rel(Num, Rel, Mono) :- 
  mk_mono_iff(Num, Rel, Imp), 
  mk_mono(Num, Imp, Mono).

par_is_fresh(_, Var) :- 
  var(Var).

par_is_fresh(_, Exp) :- 
  atomic(Exp).

par_is_fresh(Par, Exp) :- 
  \+ var(Exp), 
  \+ atomic(Exp),
  Exp = @(Num),
  Num < Par.

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

hyp_form(+ Form, Form).
hyp_form(- Form, Form).

fresh_par(Var, _) :- 
  var(Var),
  write("Error : cannot compute fresh parameter for a logic variable\n"),
  throw(unexpected_logic_variable).

fresh_par(Term, Succ) :- 
  Term = @(Num),
  Succ is Num + 1.

fresh_par(Term, 0) :- 
  Term \= @(_),
  atomic(Term).

fresh_par(Exp, Par) :- 
  Exp \= @(_),
  \+ atomic(Exp), 
  Exp =.. [_ | Exps], 
  maplist_cut(fresh_par, Exps, Nums), 
  max_list(Nums, Par).

no_new_par(FP, Exp) :- 
  fresh_par(Exp, ExpFP),
  ExpFP =< FP.

max(NumA, NumB, Max) :-
max_list([NumA, NumB], Max).

mk_mono(0, Cons, Cons).

mk_mono(Num, Cons, ! ! ((#(1) = #(0)) => Mono)) :-
  num_pred(Num, Pred), 
  mk_mono(Pred, Cons, Mono), !.

map_var_form(Goal, Num, ! Form, ! NewForm) :- 
  Succ is Num + 1,
  map_var_form(Goal, Succ, Form, NewForm).

map_var_form(Goal, Num, ? Form, ? NewForm) :- 
  Succ is Num + 1,
  map_var_form(Goal, Succ, Form, NewForm).

map_var_form(Goal, Num, FormA & FormB, NewFormA & NewFormB) :- 
  map_var_form(Goal, Num, FormA, NewFormA),
  map_var_form(Goal, Num, FormB, NewFormB).

map_var_form(Goal, Num, FormA | FormB, NewFormA | NewFormB) :- 
  map_var_form(Goal, Num, FormA, NewFormA),
  map_var_form(Goal, Num, FormB, NewFormB).

map_var_form(Goal, Num, FormA => FormB, NewFormA => NewFormB) :- 
  map_var_form(Goal, Num, FormA, NewFormA),
  map_var_form(Goal, Num, FormB, NewFormB).

map_var_form(Goal, Num, FormA <=> FormB, NewFormA <=> NewFormB) :- 
  map_var_form(Goal, Num, FormA, NewFormA),
  map_var_form(Goal, Num, FormB, NewFormB).

map_var_form(Goal, Num, ~ Form, ~ NewForm) :- 
  map_var_form(Goal, Num, Form, NewForm).

map_var_form(_, _, $true, $true).
map_var_form(_, _, $false, $false).

map_var_form(Goal, Num, Atom, NewAtom) :- 
  \+ molecular(Atom),
  Atom \= $true,
  Atom \= $false,
  Atom =.. [Rel | Terms],  
  maplist(map_var_term(call(Goal, Num)), Terms, NewTerms),
  NewAtom =.. [Rel | NewTerms].

map_var_term(_, Var, Var) :- 
  var(Var). 

map_var_term(Goal, Term, Rst) :- 
  \+ var(Term),
  Term = #(Num),
  call(Goal, Num, Rst). 

map_var_term(_, Term, @(Num)) :- 
  \+ var(Term),
  Term = @(Num).

map_var_term(Goal, Term, Fun ^ NewTerms) :- 
  \+ var(Term),
  Term = (Fun ^ Terms),  
  maplist(map_var_term(Goal), Terms, NewTerms).

orient(OPF, ONF, l, OPF, ONF) :- 
  OPF = (_, (+ _)),
  ONF = (_, (- _)).

orient(ONF, OPF, r, OPF, ONF) :- 
  OPF = (_, (+ _)),
  ONF = (_, (- _)).

strip_fas(Form, 0, Form) :-
  Form \= (! _).

strip_fas(! Form, Num, Body) :-
  strip_fas(Form, Pred, Body), 
  Num is Pred + 1.

add_fas(0, Form, Form). 

add_fas(Num, Form, ! NewForm) :-
  num_pred(Num, Pred), 
  add_fas(Pred, Form, NewForm).

add_exs(0, Form, Form). 

add_exs(Num, Form, ? NewForm) :-
  num_pred(Num, Pred), 
  add_exs(Pred, Form, NewForm).

count_fas(Form, Num) :- 
  strip_fas(Form, Num, _).

insert(Elem, Set, NewSet) :- 
  sort([Elem | Set], NewSet).

first_syn([ElemA | List], ElemB, Num) :- 
  ElemA == ElemB -> 
  Num = 0 ; 
  (
    first_syn(List, ElemB, Pred),
    Num is Pred + 1
  ).

remove_at(0, [_ | List], List). 

remove_at(Num, [Elem | List], [Elem | Rest]) :- 
  num_pred(Num, Pred), 
  remove_at(Pred, List, Rest).

remove_once_syn([ElemA | List], ElemB, List) :- 
  ElemA == ElemB.

remove_once_syn([ElemA | List], ElemB, [ElemA | Rest]) :- 
  ElemA \== ElemB,
  remove_once_syn(List, ElemB, Rest).

remove_once(Goal, [Elem | List], NewList) :- 
  call(Goal, Elem) -> 
  NewList = List ; 
  (
    remove_once(Goal, List, Rest), 
    NewList = [Elem | Rest]
  ).
  
fid_osf((Ctx, _, _), FIDs, FID, (OS, SF)) :- 
  nth0(OS, FIDs, FID),
  nth0(OS, Ctx, SF).

isf_id_sf(ID + Form, ID, + Form).
isf_id_sf(ID - Form, ID, - Form).

id_isf(ID, ISF) :- 
  isf_id_sf(ISF, ID, _).

id_sf_isf(ID, SF, ISF) :- 
  isf_id_sf(ISF, ID, SF).

goal_fresh_par((Ctx, _), Par) :- 
  fresh_par(Ctx, Par).

fst((X, _), X).
snd((_, Y), Y).

num_range(0, []). 
num_range(Num, [Pred | Nums]) :- 
  num_pred(Num, Pred),  
  num_range(Pred, Nums). 

% number_varlet(Num, "x") :- 0 is Num mod 6.
% number_varlet(Num, "y") :- 1 is Num mod 6.
% number_varlet(Num, "z") :- 2 is Num mod 6.
% number_varlet(Num, "w") :- 3 is Num mod 6.
% number_varlet(Num, "v") :- 4 is Num mod 6.
% number_varlet(Num, "u") :- 5 is Num mod 6.
% 
% number_varnum(Num, Sub) :-
%   Quo is Num div 6,
%   number_string(Quo, Sub).
% 
% var_atom(Num, Atom) :-
%   number_letter(Num, Ltr),
%   number_subscript(Num, Sub),
%   string_concat(Ltr, Sub, Str),
%   atom_string(Atom, Str).
% 
% fix_variables(_, []).
% 
% fix_variables(Num, [X | Xs]) :-
%   var_atom(Num, X),
%   SuccNum is Num + 1,
%   fix_variables(SuccNum, Xs).
% 

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
      Lines = [Line | Rest],
      read_lines_core(Stream, Rest)
    )
  ).

read_lines(File, Lines) :-
  open(File, read, Stream), 
  read_lines_core(Stream, Lines), 
  close(Stream).

string_split_with(Str, Sep, Fst, Snd) :- 
  string_concat(Fst, Rest, Str), 
  string_concat(Sep, Snd, Rest). 

string_number(Str, Num) :- 
  number_string(Num, Str).

invert_sf(+ FORM, - FORM).
invert_sf(- FORM, + FORM).
   
fof_form(_, $true, $true).
fof_form(_, $false, $false).

fof_form(Vars, ~ TPTP, ~ Form) :- 
 fof_form(Vars, TPTP, Form), !.

fof_form(Vars, ! [Var] : TPTP, ! Form)  :- 
  fof_form([Var | Vars], TPTP, Form), !.

fof_form(Vars, ! [Var | Rem] : TPTP, ! Form)  :- 
  fof_form([Var | Vars], ! Rem : TPTP, Form), !.

fof_form(Vars, ? [Var] : TPTP, ? Form)  :- 
  fof_form([Var | Vars], TPTP, Form), !.

fof_form(Vars, ? [Var | Rem] : TPTP, ? Form)  :- 
  fof_form([Var | Vars], ? Rem : TPTP, Form), !.

% fof_form(Vars, ~~~TPTP, Form) :-
%   fof_form(Vars, ~ ~ ~ TPTP, Form), !.

% fof_form(Vars, ~~TPTP, Form) :- 
%   fof_form(Vars, ~ ~ TPTP, Form), !.

fof_form(Vars, (TPTP_A \= TPTP_B), ~ (TermA = TermB)) :- 
  tptp_term(Vars, TPTP_A, TermA), !,
  tptp_term(Vars, TPTP_B, TermB), !.

fof_form(Vars, TPTP_A & TPTP_B, FormA & FormB) :- 
  fof_form(Vars, TPTP_A, FormA), !,
  fof_form(Vars, TPTP_B, FormB), !.

fof_form(Vars, TPTP_A | TPTP_B, FormA | FormB) :- 
  fof_form(Vars, TPTP_A, FormA), !,
  fof_form(Vars, TPTP_B, FormB), !.

fof_form(Vars, TPTP_A => TPTP_B, FormA => FormB) :- 
  fof_form(Vars, TPTP_A, FormA), !,
  fof_form(Vars, TPTP_B, FormB), !.

fof_form(Vars, TPTP_A <=> TPTP_B, FormA <=> FormB) :- 
  fof_form(Vars, TPTP_A, FormA), !,
  fof_form(Vars, TPTP_B, FormB), !.

fof_form(Vars, TF_A '~|' TF_B, ~ (FORM_A | FORM_B)) :- 
  fof_form(Vars, TF_A, FORM_A), !,
  fof_form(Vars, TF_B, FORM_B), !.

fof_form(Vars, TF_A ~& TF_B, ~ (FORM_A & FORM_B)) :- 
  fof_form(Vars, TF_A, FORM_A), !,
  fof_form(Vars, TF_B, FORM_B), !.

fof_form(Vars, TF_A <= TF_B, FORM_B => FORM_A) :- 
  fof_form(Vars, TF_A, FORM_A), !,
  fof_form(Vars, TF_B, FORM_B), !.

fof_form(Vars, TPTP_A <~> TPTP_B, ~ (FormA <=> FormB)) :- 
  fof_form(Vars, TPTP_A, FormA), !,
  fof_form(Vars, TPTP_B, FormB), !.

fof_form(Vars, TPTP, Form) :- 
  atom_tptp(TPTP),
  TPTP =.. [Rel | TPTPs], 
  maplist_cut(tptp_term(Vars), TPTPs, Terms),
  Form =.. [Rel | Terms], !.

tptp_term(Vars, Var, #(Num)) :- 
  var(Var),
  where(Var, Vars, Num), !.

tptp_term(Vars, TPTP, Fun ^ Terms) :- 
  TPTP =.. [Fun | TPTPs], 
  maplist_cut(tptp_term(Vars), TPTPs, Terms), !.

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

hyp((fof, TYPE, TF)) :- 
  fof(_, TYPE, TF).

hyp((cnf, TYPE, TF)) :- 
  cnf(_, TYPE, TF).

tf_form(fof, TF, FORM) :-
  fof_form([], TF, FORM).

tf_form(cnf, TF, FORM) :- 
  term_variables(TF, VARS), 
  length(VARS, NUM),
  fof_form(VARS, TF, TEMP), 
  add_fas(NUM, TEMP, FORM).

tuple_sf((LNG, TYPE, TF), + FORM) :- 
  member(TYPE, [axiom, lemma, hypothesis, definition, negated_conjecture]),
  tf_form(LNG, TF, FORM).

tuple_sf((LNG, conjecture, TF), - FORM) :- 
  tf_form(LNG, TF, FORM).

tptp_prob(TPTP, PROB) :- 
  trim_consult(TPTP),
  findall(TUPLE, hyp(TUPLE), TUPLES), 
  maplist_cut(tuple_sf, TUPLES, PROB).

put_bytes(_, []).

put_bytes(Stream, [Byte | Bytes]) :- 
  put_byte(Stream, Byte),
  put_bytes(Stream, Bytes).

codes_bytes(CDS, BTS, TAIL) :- 
  reverse(CDS, REV), 
  append([91 | REV], TAIL, BTS).

string_bytes(STR, BYTES, TAIL) :- 
  string_codes(STR, CDS), 
  codes_bytes(CDS, BYTES, TAIL).

num_bytes(NUM, BTS, TAIL) :- 
  number_string(NUM, STR), 
  string_bytes(STR, BTS, TAIL). 

atom_bytes(ATOM, BTS, TAIL) :- 
  atom_string(ATOM, STR), 
  string_bytes(STR, BTS, TAIL).

string_end_bytes(STR, BYTES, TAIL) :- 
  string_bytes(STR, BYTES, [93 | TAIL]).

% put_string_end(STRM, STR) :- 
%   put_string(STRM, STR), 
%   put_byte(STRM, 93).

break_unary_form(~ FORM, "~", FORM).
break_unary_form(! FORM, "!", FORM).
break_unary_form(? FORM, "?", FORM).
break_binary_form(FORM_A & FORM_B, FORM_A, "&", FORM_B).
break_binary_form(FORM_A | FORM_B, FORM_A, "|", FORM_B).
break_binary_form(FORM_A => FORM_B, FORM_A, "=>", FORM_B).
break_binary_form(FORM_A <=> FORM_B, FORM_A, "<=>", FORM_B).

terms_bytes([], BYTES, TAIL) :- 
  string_end_bytes(".", BYTES, TAIL).

terms_bytes([TERM | TERMS], BYTES, TAIL) :- 
  terms_bytes(TERMS, BYTES, TEMP0), !, 
  term_bytes(TERM, TEMP0, TEMP1), !, 
  string_end_bytes(",", TEMP1, TAIL).

term_bytes(#(NUM), BYTES, TAIL) :- 
  num_bytes(NUM, BYTES, TEMP), !,
  string_end_bytes("#", TEMP, TAIL).
  
term_bytes(@(NUM), BYTES, TAIL) :- 
  num_bytes(NUM, BYTES, TEMP), !,
  string_end_bytes("@", TEMP, TAIL).

term_bytes(FUN ^ TERMS, BYTES, TAIL) :- 
  terms_bytes(TERMS, BYTES, TEMP0), !,
  atom_bytes(FUN, TEMP0, TEMP1), !,
  string_end_bytes("^", TEMP1, TAIL).

form_bytes(FORM, BYTES, TAIL) :- 
  break_binary_form(FORM, LFT, CNTV, RGT) -> 
  ( form_bytes(RGT, BYTES, TEMP0), !,
    form_bytes(LFT, TEMP0, TEMP1), !,
    string_end_bytes(CNTV, TEMP1, TAIL) ) ;
  break_unary_form(FORM, CNTV, SUB) -> 
  ( form_bytes(SUB, BYTES, TEMP), !,
    string_end_bytes(CNTV, TEMP, TAIL) ) ;
  FORM =.. [REL | TERMS], !,
  terms_bytes(TERMS, BYTES, TEMP0), !,
  atom_bytes(REL, TEMP0, TEMP1), !,
  string_end_bytes("^", TEMP1, TAIL).

% put_sf(STRM, - FORM) :- 
%   put_form(STRM, FORM), 
%   pur_string_end(STRM, "-").
% 
% put_sf(STRM, + FORM) :- 
%   put_form(STRM, FORM), 
%   pur_string_end(STRM, "+").
% 
% put_form(STRM, FORM) :- 
%   break_binary_form(FORM, LFT, CNTV, RGT) -> 
%   ( put_form(STRM, RGT), 
%     put_form(STRM, LFT), 
%     put_string_end(STRM, CNTV) ) ;
%   break_unary_form(FORM, CNTV, SUB) -> 
%   ( put_form(STRM, SUB), 
%     put_string_end(STRM, CNTV) ) ;
%   FORM =.. [REL | TERMS], 
%   put_terms(STRM, TERMS), 
%   put_atom(STRM, REL),  
%   string_end_bytes(^, BYTES, TEMP).

sf_bytes(- FORM, BYTES, TAIL) :- 
  form_bytes(FORM, BYTES, TEMP), 
  string_end_bytes("-", TEMP, TAIL).

sf_bytes(+ FORM, BYTES, TAIL) :- 
  form_bytes(FORM, BYTES, TEMP), 
  string_end_bytes("+", TEMP, TAIL).

prob_bytes([], BYTES, BYTES).

prob_bytes([SF | PROB], BYTES, TAIL) :- 
  prob_bytes(PROB, BYTES, TEMP),
  sf_bytes(SF, TEMP, TAIL). 

% put_prob(_, []).
% 
% put_prob(STRM, [SF | PROB]) :- 
%   put_prob(STRM, PROB), 
%   put_sf(STRM, SF). 

export_tptp(TPTP, TXTX) :- 
  write("0\n"),
  tptp_prob(TPTP, PROB), 
  write("1\n"),
  prob_bytes(PROB, BYTES, []),
  write("2\n"),
  open(TXTX, write, STRM, [encoding(octet)]),
  write("3\n"),
  put_bytes(STRM, BYTES),
  write("4\n"),
  close(STRM).
  