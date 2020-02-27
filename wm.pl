:- [compile].

str_dir(Str, (Dir, Nums)) :- 
  split_string(Str, ".", "", [DirStr | DirStrs]), 
  term_string(Dir, DirStr), 
  maplist_cut(string_number, DirStrs, Succs), 
  maplist_cut(num_pred, Succs, Nums). 

/*

varcount(? Form, Cnt) :- 
  varcount(Form, Temp), 
  Cnt is Temp + 1.

varcount(! Form, Cnt) :- 
  varcount(Form, Temp), 
  Cnt is Temp + 1.

varcount(Form, 0) :- 
  Form \= (! _),
  Form \= (? _).

mk_variable(Num, Var) :- 
  atomics_to_string(["var", Num, " : ANY"], Var).

mk_variables(Eqs, ["VARIABLES" | Vars]) :- 
  maplist_cut(varcount, Eqs, Nums), 
  max_list(Nums, Num), 
  num_range(Num, Rng), 
  maplist_cut(mk_variable, Rng, Vars).

atom_wma(Atom, WMT) :- 
  Atom =.. [_ | Terms], 
  maplist_cut(mk_wmt, Terms, WMTs), 
  WMT =.. [placeholder | WMTs].


atom_wma_str(Atom, WMA_str) :- 
  atom_wma(Atom, WMA),
  term_string(WMA, WMA_str).

eqv_wmeq(AtomA <=> AtomB, Weq) :- 
  atom_wma_str(AtomA, WMA_str_A),
  atom_wma_str(AtomB, WMA_str_B),
  atomics_to_string([WMA_str_A, " = ", WMA_str_B], Weq).
  

faeq_wmeq(Eq, WMeq) :- 
  Eq \= (! _), 
  eq_wmeq(Eq, WMeq).

faeq_wmeq(! FAEq, WMeq) :- 
  faeq_wmeq(FAEq, WMeq).

exeqv_wmeq(Eq, WMeq) :- 
  Eq \= (? _), 
  eqv_wmeq(Eq, WMeq).

exeqv_wmeq(? FAEq, WMeq) :- 
  exeqv_wmeq(FAEq, WMeq).


mk_eqv_conc(Eqv, ["CONCLUSION", WMEq]) :- 
  exeqv_wmeq(Eqv, WMEq).

mk_eqv_problem(FormA, FormB, PR) :- 
  Header = ["NAME TEMP", "MODE PROOF", "SORTS ANY"], 
  faeq_farities(FormA, FAsA),
  exeqv_farities(FormB, FAsB),
  union(FAsA, FAsB, FAs),
  mk_signature(FAs, Sig), !,  
  mk_ordering(FAs, Ord), !, 
  mk_variables([FormA, FormB], Vars), !, 
  mk_equations([FormA], Eqs), !, 
  mk_eqv_conc(FormB, Conc), !,
  append([Header, Sig, Ord, Vars, Eqs, Conc], PR).

% eqs(EqISFs, ONF, IPP) :-
%   ONF = (_, (- (TermA = TermB))), 
%   \+ var(TermA),
%   \+ var(TermB),
%   TermA = (Fun ^ TermsA),
%   TermB = (Fun ^ TermsB),
%   length(TermsA, Lth),
%   length(TermsB, Lth),
%   maplist_cut(equatable(EqISFs), TermsA, TermsB),
%   mk_mono_fun(Lth, Fun, MonoForm),
%   i_h(+ MonoForm, mono_fun(Fun, Lth), IPP, Mono, IPP0),
%   prv_mono(Mono, TermsA, EqISFs, TermsB, IPP0, ISF, IPP1),
%   i_x(ISF, ONF, IPP1).


exeqv_farities(? Form, FAs) :-
  exeqv_farities(Form, FAs).

exeqv_farities(Form, FAs) :-
  Form \= (? _), 
  eqv_farities(Form, FAs).

faeq_farities(! Form, FAs) :-
  faeq_farities(Form, FAs).

faeq_farities(Form, FAs) :-
  Form \= (! _), 
  eq_farities(Form, FAs).

eqv_farities(AtomA <=> AtomB, FAs) :-
  atom_farities(AtomA, FAsA),
  atom_farities(AtomB, FAsB),
  union(FAsA, FAsB, FAs).


atom_farities(Atom, FAs) :-
  Atom =.. [_ | Terms], 
  length(Terms, Lth), 
  maplist_cut(term_farities, Terms, FAss), 
  union([[(placeholder, Lth)] | FAss], FAs).

opa_eqs_ona(Mode, OPA, EqISFs, ONA, IPP) :- 
  OPA = (_, (+ AtomA)),
  ONA = (_, (- AtomB)),
  AtomA =.. [Rel | TermsA], 
  AtomB =.. [Rel | TermsB], 
  length(TermsA, Lth),
  length(TermsB, Lth),
  maplist_cut(equatable(EqISFs), TermsA, TermsB),
  mk_mono_rel(Lth, Rel, MonoForm),
  i_h(+ MonoForm, mono_rel(Rel, Lth), IPP, Mono, IPP0),
  prv_mono(Mode, Mono, TermsA, EqISFs, TermsB, IPP0, Cons, IPP1),
  i_b(Cons, IPP1, ISF2, IPP2, ISF3, IPP3), 
  i_x(OPA, ISF2, IPP2), 
  i_x(ISF3, ONA, IPP3). 



% wm_eqv(OPEq, ONEqv, DFP) :- 
%   opf_form(OPEq, FormA),
%   onf_form(ONEqv, FormB),
%   mk_eqv_problem(FormA, FormB, Prob),
%   write_list_file("temp.pr", Prob), !,
%   shell("waldmeister temp.pr > temp.sol", _), !,
%   file_wm_prf("temp.sol", WMLs), 
%   write("Begin WM proof:\n\n"),
%   write_list(WMLs),
%   % maplist(mk_wosf, OPEqs, WOSFs),
%   % mk_wosf(ONEq, WOSF),
%   % use_wmls(WMLs, [WOSF | WOSFs], DFP, OSF, NewDFP),
%   % eq_refl(OSF, NewDFP).
%   false.

  % ONF = (_, (- (TermA = TermB))), 
  % \+ var(TermA),
  % \+ var(TermB),
  % TermA = (Fun ^ TermsA),
  % TermB = (Fun ^ TermsB),
  % length(TermsA, Lth),
  % length(TermsB, Lth),
  % maplist_cut(equatable(EqISFs), TermsA, TermsB),
  % mk_mono_fun(Lth, Fun, MonoForm),
  % i_h(+ MonoForm, mono_fun(Fun, Lth), IPP, Mono, IPP0),
  % prv_mono(nv, Mono, TermsA, EqISFs, TermsB, IPP0, ISF, IPP1),
  % i_x(ISF, ONF, IPP1).

eqs(nv, _, ONF, DFP) :- 
  ONF = (_, (- (TermA = TermB))), 
  unify_with_occurs_check(TermA, TermB),
  eq_refl(ONF, DFP).

eqs(nv, EqISFs, ONF, IPP) :-
  ONF = (_, (- (TermA = TermB))), 
  \+ var(TermA),
  \+ var(TermB),
  TermA = (Fun ^ TermsA),
  TermB = (Fun ^ TermsB),
  length(TermsA, Lth),
  length(TermsB, Lth),
  maplist_cut(equatable(EqISFs), TermsA, TermsB),
  mk_mono_fun(Lth, Fun, MonoForm),
  i_h(+ MonoForm, mono_fun(Fun, Lth), IPP, Mono, IPP0),
  prv_mono(nv, Mono, TermsA, EqISFs, TermsB, IPP0, ISF, IPP1),
  i_x(ISF, ONF, IPP1).

eqs(nv, EqISFs, INF, IPP) :- 
  INF = (_, (- (TermA = TermC))), 
  pluck(EqISFs, EqISF, Rest),
  many_nb([c], [EqISF], IPP, [ISF0], IPP0), 
  ISF0 = (_, (+ TermA_p = TermB)),
  unify_with_occurs_check(TermA, TermA_p), 
  i_f(TermB = TermC, IPP0, ISF1, IPP1, ISF2, IPP2), 
  eqs(nv, Rest, ISF1, IPP1), 
  eq_trans(ISF0, ISF2, INF, IPP2).

eqs(nv, EqISFs, INF, IPP) :- 
  INF = (_, (- TermA = TermC)), 
  pluck(EqISFs, EqISF, Rest),
  many_nb([c], [EqISF], IPP, [ISF0], IPP0), 
  ISF0 = (_, (+ TermB = TermA_p)),
  unify_with_occurs_check(TermA, TermA_p), 
  i_f(TermA_p = TermB, IPP0, INF0, IPP1, IPF0, IPP2), 
  eq_symm(ISF0, INF0, IPP1), 
  i_f(TermB = TermC, IPP2, INF1, IPP3, IPF1, IPP4), 
  eqs(nv, Rest, INF1, IPP3), 
  eq_trans(IPF0, IPF1, INF, IPP4).

dfp_fp((_, FP, _), FP).

a_osf((_, SF)) :-
  b_a(l, SF, _).

b_osf((_, SF)) :-
  b_b(SF, _, _).

c_osf((_, SF)) :-
  b_c(_, SF, _).

d_osf((_, SF)) :-
  b_d(0, SF, _).

n_osf((_, SF)) :-
  b_n(SF, _).

% sup_wm(OPF, OPEq, OSFs, DFP) :- 
%   maplist(snd, OSFs, SFs),
%   OPF = (_, PF),
%   \+ pos_fas_lit(PF),
%   isolate_pivot(PF, SFs, Form), 
%   i_f(Form, DFP, ONF_L, DFP0, OPF_R, DFP1), 
%   opqla_onqla(OPF, ONF_L, DFP0), 
%   i_b(OPF_R, DFP1, OPLit, DFP2, OPCla, DFP3), 
%   close_opcla(OSFs, OPCla, DFP3),
%   member(OSF, OSFs), 
%   mk_ex_eq(OPLit, OSF, Eqv), 
%   i_f(Eqv, DFP2, ONEqv, DFP4, OPEqv, DFP5), 
%   close_opeqv(OPLit, OPEqv, OSF, DFP5),
%   wm_eqv(OPEq, ONEqv, DFP4).


wm(OPEQS, ONEQ, DFP) :- 
  % maplist(snd, OSFs, SFs),
  OPF = (_, PF),
  pos_fas_lit(PF),
  member(OSF, OSFs), 
  mk_ex_eq(OPF, OSF, Eqv), 
  i_f(Eqv, DFP, ONEqv, DFP0, OPEqv, DFP1), 
  close_opeqv(OPF, OPEqv, OSF, DFP1),
  wm_eqv(OPEq, ONEqv, DFP0).

*/

pair_farities((TERM_A, TERM_B), FAS) :-
  term_farities(TERM_A, FAS_A),
  term_farities(TERM_B, FAS_B),
  union(FAS_A, FAS_B, FAS).

term_farities(Term, []) :-
  \+ var(Term),
  Term = #(_).

term_farities(Term, [(ParNum, 0)]) :-
  \+ var(Term),
  Term = @(Num), 
  atomic_concat(parameter, Num, ParNum).

term_farities(Term, FAs) :- 
  \+ var(Term),
  Term = (Fun ^ Terms),  
  length(Terms, Lth), 
  maplist_cut(term_farities, Terms, FAss), 
  union([[(Fun, Lth)] | FAss], FAs).

mk_type(0, " -> ANY").

mk_type(Num, Type) :- 
  num_pred(Num, Pred), 
  mk_type(Pred, Cons), 
  string_concat(" ANY", Cons, Type).

mk_decl((Fun, Num), Decl) :- 
  mk_type(Num, Type), 
  atomics_to_string([Fun, ":", Type], Decl).

mk_variables(_, ["VARIABLES"]).

mk_signature(FAs, ["Signature" | Decls]) :- 
  maplist_cut(mk_decl, FAs, Decls).

mk_ordering_core([Fun], FunStr) :-
  atom_string(Fun, FunStr).

mk_ordering_core([Fun | Funs], Ord) :-
  mk_ordering_core(Funs, TempOrd), 
  atomics_to_string([Fun, " > ", TempOrd], Ord).

mk_ordering(FAs, ["ORDERING LPO", Ord]) :- 
  maplist_cut(fst, FAs, Funs), 
  mk_ordering_core(Funs, Ord).

% term_wmt(#(Num), Term) :- 
%   atomic_concat("var", Num, Term).

term_wmt(@(Num), Term) :- 
  atomic_concat("parameter", Num, Term).

term_wmt((FUN ^ TERMS), WMT) :- 
  maplist_cut(term_wmt, TERMS, WMTS), 
  WMT =.. [FUN | WMTS].

term_wmt_str(TERM, WMT_STR) :- 
  term_wmt(TERM, WMT),
  term_string(WMT, WMT_STR).

pair_eqn((TERM_A, TERM_B), EQN) :- 
  term_wmt_str(TERM_A, WMT_STR_A),
  term_wmt_str(TERM_B, WMT_STR_B),
  atomics_to_string([WMT_STR_A, " = ", WMT_STR_B], EQN).

mk_equations(PAIRS, ["EQUATIONS" | EQNS]) :- 
  maplist_cut(pair_eqn, PAIRS, EQNS).

mk_conclusion(PAIR, ["CONCLUSION", EQN]) :- 
  pair_eqn(PAIR, EQN).

mk_problem(PAIRS, PAIR, PROB) :- 
  Header = ["NAME TEMP", "MODE PROOF", "SORTS ANY"], 
  maplist_cut(pair_farities, [PAIR | PAIRS], FASS),
  union(FASS, FAS),
  mk_signature(FAS, SIG), !,  
  mk_ordering(FAS, ORD), !, 
  mk_variables(_, VARS), !, 
  mk_equations(PAIRS, PREMS), !, 
  mk_conclusion(PAIR, CONC), !,
  append([Header, SIG, ORD, VARS, PREMS, CONC], PROB).

% osf_form(OSF, Form) :- 
%   opf_form(OSF, Form) ;
%   onf_form(OSF, Form).

opeq_pair((_, (+ TERM_A = TERM_B)), (TERM_A, TERM_B)).
oneq_pair((_, (- TERM_A = TERM_B)), (TERM_A, TERM_B)).

id_sign(ID, '+') :-
  string_concat("0", _, ID). 

id_sign(ID, '-') :-
  string_concat("1", _, ID). 

mk_jst_aux("initial", repeat(none)). 

mk_jst_aux("hypothesis", repeat(none)). 

mk_jst_aux(Str, repeat(ID)) :- 
  term_string(orient(Temp, _), Str),
  term_string(Temp, ID).

mk_jst_aux(Str, tes_red(ID0, Dir0, ID1, Dir1)) :- 
  string_lower(Str, LowStr),
  string_concat("tes-red(", Str0, LowStr),
  string_concat(Str1, ")", Str0),
  split_string(Str1, ",", "", [ID0, DirStr0, ID1, DirStr1]), 
  str_dir(DirStr0, Dir0), 
  str_dir(DirStr1, Dir1). 

  % term_string(tes - red(Temp0, PreDir0, Temp1, PreDir1), LowStr),
  % term_string(Temp0, ID0),
  % term_string(Temp1, ID1),
  % term_string(PreDir0, DirStr0),
  % term_string(PreDir1, DirStr1),
  % split_string(DirStr, ".", "", [Dir0 | ])
  

mk_jst_aux(ID, repeat(ID)) :- 
  string_codes(ID, [Code | _]), 
  (Code = 48 ; Code = 49).

mk_jst(JSTStr, JST) :- 
  (
    string_split_with(JSTStr, " ###", Fst, _) -> 
    mk_jst_aux(Fst, JST) ;
    mk_jst_aux(JSTStr, JST)
  ).

% wmt_term(#(Num), Num, #(Pred)) :- 
%   num_pred(Num, Pred).

wmt_term(WMT, @(NUM)) :- 
  atom(WMT),
  atom_string(WMT, STR), 
  string_concat("parameter", NUM_STR, STR),
  number_string(NUM, NUM_STR).

wmt_term(WMT, FUN ^ TERMS) :- 
  % WMT \= #(_), 
  WMT =.. [FUN | WMTS], 
  maplist_cut(wmt_term, WMTS, TERMS).
  % max_list([0 | Maxes], Max). 

wmf_form(WMF, TERM_A = TERM_B) :- 
  re_replace("X([0-9]+)"/g, "#($1)", WMF, TEMP),
  (
    term_string(WMT_A = WMT_B, TEMP) ;
    term_string(WMT_A -> WMT_B, TEMP)
  ), 
  wmt_term(WMT_A, TERM_A),
  wmt_term(WMT_B, TERM_B).
  % max(Max0, Max1, Max),
  % add_fas(Max, Term0 = Term1, Form).

string_wml(STR, (ID, TYPE, SF, JST)) :- 
  split_string(STR, ":", " ", [ID, TYPE, WMF, JST_STR]), 
  id_sign(ID, SIGN), 
  wmf_form(WMF, FORM),
  SF =.. [SIGN, FORM],
  mk_jst(JST_STR, JST).

file_wmls(FILE, WMLS) :-
  file_strings(FILE, STRS), 
  maplist_try(string_wml, STRS, WMLS), !.

mk_wosf(OSF, (none, OSF)).

use_wml((ID, _, SF, repeat(PID)), Ctx, DFP, (ID, OSF), DFP) :- 
  member((PID, OSF), Ctx), 
  OSF = (_, SF).

use_wml((ID, _, (+ Form), repeat(PID)), Ctx, DFP, (ID, OPF), NewDFP) :- 
  i_f(Form, DFP, ONF, TempDFP, OPF, NewDFP), 
  many_nb([d], [ONF], TempDFP, [OSF0], DFP0), 
  member((PID, OSF), Ctx), 
  OSF = (_, (+ _)),
  many_nb([c], [OSF], DFP0, [OSF1], DFP1), 
  mate(OSF0, OSF1, DFP1). 

use_wml((ID, _, (- Form), repeat(PID)), Ctx, DFP, (ID, ONF), NewDFP) :- 
  i_f(Form, DFP, ONF, NewDFP, OPF, TempDFP), 
  member((PID, OSF), Ctx), 
  OSF = (_, (- _)),
  many_nb([d], [OSF], TempDFP, [OSF0], DFP0), 
  many_nb([c], [OPF], DFP0, [OSF1], DFP1), 
  mate(OSF0, OSF1, DFP1). 

use_wml((ID, _, SF, tes_red(PID0, (Dir, Nums), PID1, (l, []))), Ctx, DFP, (ID, NewOSF), NewDFP) :- 
  i_f_s(SF, DFP, OSF_A, DFP0, NewOSF, NewDFP), 
  member((PID0, OSF_B), Ctx), 
  member((PID1, OPEq0), Ctx), 
  orient(OSF_A, OSF_B, _, OPF, ONF), 
  many_nb([d], [ONF], DFP0, [ONF0], DFP1), 
  many_nb([c], [OPF], DFP1, [OPF0], DFP2), 
  many_nb([c], [OPEq0], DFP2, [OPEq1], DFP3), 
  ONF0 = (_, (- TermA = TermC)),
  (
    Dir = l -> 
    (
      OPF0 = (_, (+ TermB = TermC)), 
      i_f(TermA = TermB, DFP3, ONEq, DFP4, OPAB, TempDFP0), 
      eq_trans(OPAB, OPF0, ONF0, TempDFP0) 
    ) ;
    (
      OPF0 = (_, (+ TermA = TermB)),  
      i_f(TermB = TermC, DFP3, ONEq, DFP4, OPBC, TempDFP0), 
      eq_trans(OPF0, OPBC, ONF0, TempDFP0) 
    ) 
  ), 
  ( 
    (  
      (id_sign(ID, '+'), Dir = r) ; 
      (id_sign(ID, '-'), Dir = l)  
    ) -> 
    (OPEq = OPEq1, TempDFP1 = DFP4) ; 
    eq_symm(OPEq1, DFP4, OPEq, TempDFP1)
  ),
  use_rw(Nums, OPEq, ONEq, TempDFP1).
  
force_break_eq(ONE, DFP, ODFPs) :- 
  ONE = (_, (- TermA = TermB)),
  \+ var(TermA),
  \+ var(TermB),
  TermA = (Fun ^ TermsA),
  TermB = (Fun ^ TermsB),
  length(TermsA, Lth),
  length(TermsB, Lth),
  % maplist_cut(term_poseq_term(OPEs), TermsA, TermsB),
  mk_mono_fun(Lth, Fun, MonoForm),
  i_h(+ MonoForm, mono_fun(Fun, Lth), DFP, Mono, DFP0),
  intro_eqs(Mono, TermsA, TermsB, DFP0, OPE, ODFPs, DFP1),
  i_x(OPE, ONE, DFP1).

use_rw([], OPEq, ONEq, DFP) :-  
  OPEq = (_, (+ TermA = TermB)),
  ONEq = (_, (- TermA = TermB)),
  mate(OPEq, ONEq, DFP).

use_rw([Num | Nums], OPEq, ONEq, DFP) :-  
  force_break_eq(ONEq, DFP, EDFPs), 
  use_rw_aux(Num, Nums, OPEq, EDFPs).

use_rw_aux(Num, Nums, OPEq, [EDFP | EDFPs]) :- 
  num_pred(Num, Pred), 
  use_rw_refl(EDFP), 
  use_rw_aux(Pred, Nums, OPEq, EDFPs). 

use_rw_aux(0, Nums, OPEq, [(ONEq, DFP) | EDFPs]) :- 
  use_rw(Nums, OPEq, ONEq, DFP),  
  maplist_cut(use_rw_refl, EDFPs).

use_rw_refl((ONEq, DFP)) :- 
  eq_refl(ONEq, DFP).

use_wmls([], [(_, OSF) | _], DFP, OSF, DFP).

use_wmls([WML | WMLs], Ctx, DFP, LastOSF, NewDFP) :-
  use_wml(WML, Ctx, DFP, NewWOSF, TempDFP), 
  use_wmls(WMLs, [NewWOSF | Ctx], TempDFP, LastOSF, NewDFP).

wm(OPEQS, ONEQ, DFP) :- 
  maplist(opeq_pair, OPEQS, PAIRS), 
  oneq_pair(ONEQ, PAIR), !,
  mk_problem(PAIRS, PAIR, PROB),
  write_list_file("temp.pr", PROB), !,
  shell("waldmeister temp.pr > temp.sol", _), !,
  delete_file("temp.pr"),
  file_wmls("temp.sol", WMLS), 
  delete_file("temp.sol"),
  write("Begin WM proof:\n\n"),
  write_list(WMLS),
  maplist(mk_wosf, OPEQS, WOSFS),
  mk_wosf(ONEQ, WOSF),
  use_wmls(WMLS, [WOSF | WOSFS], DFP, NEW_OSF, NEW_DFP),
  eq_refl(NEW_OSF, NEW_DFP).