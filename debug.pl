:- [debug_trace].

debug :- 
  debug_prvr(PRVR), 
  debug_hints(HINTS), 
  debug_ctx(CTX), 
  debug_hyp(HYP), 
  debug_goal(GOAL), 
  % debug_hint(HINT), 
  % debug_prems(Prems), 
  % debug_conc(Conc),
  % debug_rul(Rul), 
  % debug_fids(FIDs), 
  % debug_ctx(Ctx), 
  % open("debug_output", write, STRM, [encoding(octet)]),
  infer(PRVR, HINTS, CTX, HYP, GOAL).
  
  % (
  %   PROVER = vampire -> 
  %   v_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) ;  
  %   m_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) 
  % ).
