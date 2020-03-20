:- [debug_trace].

debug :- 
  debug_prvr(PRVR), 
  debug_hints(HINTS), 
  debug_ctx(CTX), 
  debug_hyp(HYP), 
  debug_goal(GOAL), 
  infers(PRVR, HINTS, CTX, HYP, GOAL).