:- [debug_trace].

debug :- 
  debug_hint(HINT), 
  debug_fi(FI), 
  debug_goal(GOAL), 
  % debug_hint(HINT), 
  % debug_prems(Prems), 
  % debug_conc(Conc),
  % debug_rul(Rul), 
  % debug_fids(FIDs), 
  % debug_ctx(Ctx), 
  open("debug_output", write, STRM, [encoding(octet)]),
  use_hint(STRM, HINT, FI, GOAL, _, _).
  
  % (
  %   PROVER = vampire -> 
  %   v_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) ;  
  %   m_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) 
  % ).
