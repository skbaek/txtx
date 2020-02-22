:- [basic, rules].

proof(_).

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

chk(Ctx, FP, h(SF, Jst, Prf)) :-  
  no_new_par(FP, SF),
  justified(Ctx, SF, Jst), !,
  chk([SF | Ctx], FP, Prf).

chk(Ctx, FP, n(ID, Prf)) :-  
  nth0(ID, Ctx, SF),
  b_n(SF, NewSF), !, 
  chk([NewSF | Ctx], FP, Prf).

chk(Ctx, _, x(PID, NID)) :-  
  nth0(PID, Ctx, + Form),
  nth0(NID, Ctx, - Form).

prf_hypjsts(a(_, _, Prf), HypJsts) :-
  prf_hypjsts(Prf, HypJsts).

prf_hypjsts(b(_, PrfA, PrfB), HypJsts) :-
  prf_hypjsts(PrfA, HypJstsA),
  prf_hypjsts(PrfB, HypJstsB),
  union(HypJstsA, HypJstsB, HypJsts).

prf_hypjsts(c(_, _, Prf), HypJsts) :-
  prf_hypjsts(Prf, HypJsts).

prf_hypjsts(d(_, Prf), HypJsts) :-
  prf_hypjsts(Prf, HypJsts).

prf_hypjsts(f(_, PrfA, PrfB), HypJsts) :-
  prf_hypjsts(PrfA, HypJstsA),
  prf_hypjsts(PrfB, HypJstsB),
  union(HypJstsA, HypJstsB, HypJsts).

prf_hypjsts(h(SF, Jst, Prf), [(SF, Jst) | HypJsts]) :-
  prf_hypjsts(Prf, HypJsts).

prf_hypjsts(n(_, Prf), HypJsts) :-
  prf_hypjsts(Prf, HypJsts).

prf_hypjsts(x(_, _), []).

print_hypjst((Hyp, Jst)) :- 
  format('[Justification = ~w] : ~w\n', [Jst, Hyp]).

print_sig(Prf) :- 
  prf_hypjsts(Prf, HypJsts), 
  maplist(print_hypjst, HypJsts).

txtx_prf(TXTX, PRF) :-
  dynamic(proof/1),
  retractall(proof(_)),
  consult(TXTX),
  proof(PRF).

verify(TPTP, TXTX) :-
  write("Loading TPTP problem...\n\n"),
  tptp_prob(TPTP, PROB),
  write("Loading TXTX proof...\n\n"),
  txtx_prf(TXTX, PRF),
  write("Verifying proof...\n\n"),
  (
    chk(PROB, 0, PRF) -> 
    (
      write("θ-hypotheses used :\n\n"),
      print_sig(PRF),
      write("\nVerification successful.\n\n")
    ) ;
    (
      write("Warning : verification failed.\n\n"),
      false
    )
  ).