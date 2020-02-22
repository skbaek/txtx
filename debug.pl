:- [trace].

debug(PROVER) :- 
  consult("debug"), 
  debug_id(ID), 
  debug_prems(Prems), 
  debug_conc(Conc),
  debug_rul(Rul), 
  debug_fids(FIDs), 
  debug_ctx(Ctx), 
  (
    PROVER = vampire -> 
    v_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) ;  
    m_add((ID, Prems, Conc, Rul), FIDs, (Ctx, 0, _), _, _) 
  ).
