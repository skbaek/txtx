:- [basic, rules].

% proof(_).

chk(Ctx, FP, a(Dir, ID, Prf)) :- 
  nth0(ID, Ctx, SF),
  b_a(Dir, SF, NewSF), !,
  chk([NewSF | Ctx], FP, Prf).

chk(Ctx, FP, b(ID, PrfA, PrfB)) :- 
  nth0(ID, Ctx, SF),
  b_b(SF, SF_A, SF_B), !,
  chk([SF_A | Ctx], FP, PrfA), !, 
  chk([SF_B | Ctx], FP, PrfB).

chk(Ctx, FP, c(Term, ID, Prf)) :-  
  ground(Term),
  ovar_free_term(Term),
  no_new_par(FP, Term), 
  nth0(ID, Ctx, SF),
  b_c(Term, SF, NewSF), !, 
  chk([NewSF | Ctx], FP, Prf).

chk(Ctx, FP, d(ID, Prf)) :-  
  nth0(ID, Ctx, SF),
  b_d(FP, SF, NewSF),
  SuccFP is FP + 1, !, 
  chk([NewSF | Ctx], SuccFP, Prf).

chk(Ctx, FP, f(Form, PrfA, PrfB)) :-  
  ground(Form), 
  closed_form(Form),
  no_new_par(FP, Form), !, 
  chk([- Form | Ctx], FP, PrfA), !, 
  chk([+ Form | Ctx], FP, PrfB).

chk(Ctx, FP, h(SF, JST, Prf)) :-  
  no_new_par(FP, SF),
  justified(Ctx, SF, JST), !,
  chk([SF | Ctx], FP, Prf).

chk(Ctx, FP, n(ID, Prf)) :-  
  nth0(ID, Ctx, SF),
  b_n(SF, NewSF), !, 
  chk([NewSF | Ctx], FP, Prf).

chk(Ctx, _, x(PID, NID)) :-  
  nth0(PID, Ctx, + Form),
  nth0(NID, Ctx, - Form).

% print_hypjst((Hyp, JST)) :- 
%   format('[Justification = ~w] : ~w\n', [JST, Hyp]).
% 
% print_sig(Prf) :- 
%   prf_hypjsts(Prf, HypJSTs), 
%   maplist(print_hypjst, HypJSTs).

% txtx_prf(TXTX, PRF) :-
%   dynamic(proof/1),
%   retractall(proof(_)),
%   consult(TXTX),
%   proof(PRF).

verify_core(STRM, ARGS, GOAL) :-
  get_byte(STRM, CD), 
  (
    CD = 91 -> 
    (
      % write("begin\n"),
      verify_core(STRM, [[] | ARGS], GOAL)
    ) ;
    CD = 93 -> 
    (
      % write("end\n"),
      ARGS = [CDS | REST], 
      string_codes(OP, CDS),
      (
        verify_apply(STRM, OP, REST, GOAL) -> true ; 
        (
          format('OP at fail = ~w\n', OP),
          write("ARGS at fail = "), write(REST), nl,
          throw(foobar)
        )
      )
    ) ;
    % write("push\n"),
    ARGS = [CDS | REST], 
    verify_core(STRM, [[CD | CDS] | REST], GOAL)
  ).

verify_apply(STRM, "a", [PL, CL, DL], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(CID, CL),
  atom_codes(DIR, DL),
  as(none, PID, CID, DIR, GOAL, GOAL_N), 
  verify_core(STRM, [], GOAL_N), !.

verify_apply(STRM, "b", [PL, CL], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(CID, CL),
  bs(none, PID, CID, GOAL, GOAL_L, GOAL_R), !, 
  verify_core(STRM, [], GOAL_L), !,
  verify_core(STRM, [], GOAL_R), !.

verify_apply(STRM, "c", [PL, CL, TERM], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(CID, CL),
  cs(none, PID, CID, TERM, GOAL, GOAL_N), 
  verify_core(STRM, [], GOAL_N), !.

verify_apply(STRM, "d", [PL, CL], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(CID, CL),
  ds(none, PID, CID, GOAL, GOAL_N), 
  verify_core(STRM, [], GOAL_N), !.

verify_apply(STRM, "k", [CL, FORM], GOAL) :-
  atom_codes(CID, CL),
  ks(none, CID, FORM, GOAL, GOAL_L, GOAL_R), 
  verify_core(STRM, [], GOAL_L), !,
  verify_core(STRM, [], GOAL_R), !.

verify_apply(STRM, "n", [PL, CL], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(CID, CL),
  ns(none, PID, CID, GOAL, GOAL_N), !,
  verify_core(STRM, [], GOAL_N), !.

verify_apply(STRM, "t", [CL, SF | CDSS], GOAL) :-
  atom_codes(CID, CL),
  maplist(string_codes, JST, CDSS),
  ts(none, CID, SF, JST, GOAL, GOAL_N),
  verify_core(STRM, [], GOAL_N), !.

verify_apply(_, "x", [PL, NL], GOAL) :-
  atom_codes(PID, PL),
  atom_codes(NID, NL),
  xs(none, PID, NID, GOAL), !.

verify_apply(STRM, STR, [SUB_FORM | ARGS], GOAL) :-
  string_uctv(STR, CTV), 
  FORM =.. [CTV, SUB_FORM], !,
  verify_core(STRM, [FORM | ARGS], GOAL), !.

verify_apply(STRM, STR, [FORM_A, FORM_B | ARGS], GOAL) :-
  string_bctv(STR, CTV), 
  FORM =.. [CTV, FORM_A, FORM_B],
  verify_core(STRM, [FORM | ARGS], GOAL), !.

verify_apply(STRM, "#", [CDS | ARGS], GOAL) :-
  number_codes(NUM, CDS), 
  verify_core(STRM, [NUM | ARGS], GOAL), !.

verify_apply(STRM, STR, [NUM | ARGS], GOAL) :-
  string_codes(STR, [36]),
  verify_core(STRM, [#(NUM) | ARGS], GOAL), !.

verify_apply(STRM, "@", [NUM | ARGS], GOAL) :-
  verify_core(STRM, [@(NUM) | ARGS], GOAL), !.

verify_apply(STRM, "*", [STR, NUM | ARGS], GOAL) :-
  atom_string(FUN, STR),
  split_at(NUM, ARGS, TERMS, REST),
  verify_core(STRM, [(FUN ^ TERMS) | REST], GOAL), !.

verify_apply(STRM, "^", [STR, NUM | ARGS], GOAL) :-
  atom_string(REL, STR),
  split_at(NUM, ARGS, TERMS, REST),
  FORM =.. [REL | TERMS],
  verify_core(STRM, [FORM | REST], GOAL), !.

verify_apply(STRM, "T", ARGS, GOAL) :-
  verify_core(STRM, [$true | ARGS], GOAL), !.

verify_apply(STRM, "F", ARGS, GOAL) :-
  verify_core(STRM, [$false | ARGS], GOAL), !.

verify_apply(STRM, "+", [FORM | ARGS], GOAL) :-
  verify_core(STRM, [(+ FORM) | ARGS], GOAL), !.

verify_apply(STRM, "-", [FORM | ARGS], GOAL) :-
  verify_core(STRM, [(- FORM) | ARGS], GOAL), !.

string_uctv("~", '~').
string_uctv("!", '!').
string_uctv("?", '?').

string_bctv("|", '|').
string_bctv("&", '&').
string_bctv("=>", '=>').
string_bctv("<=>", '<=>').

verify(TPTP, TXTX) :-
  write("Loading TPTP problem\n"),
  tptp_prob(TPTP, PROB),
  open(TXTX, read, STRM, [encoding(octet)]),
  write("Begin verification\n"),
  (
    verify_core(STRM, [], (PROB, 0)) ->
    write("Verification successful.\n") ; 
    (
      write("Warning : verification failed.\n"),
      false
    )
  ).

  % (
  %   chk(PROB, 0, PRF) -> 
  %   (
  %     write("θ-hypotheses used :\n\n"),
  %     print_sig(PRF),
  %     write("\nVerification successful.\n\n")
  %   ) ;
  %   (
  %     write("Warning : verification failed.\n\n"),
  %     false
  %   )
  % ).