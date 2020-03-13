:- [basic].

verify(STRM, PROB, FP) :- 
  get_char(STRM, CH), 
  (
    CH = 'A' -> 
    get_id(STRM, PID),  
    get_dir(STRM, DIR),
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    ab(DIR, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N),
    verify(STRM, PROB_N, FP) ;

    CH = 'B' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    bb(PREM, CONC_L, CONC_R),
    put_assoc(CID, PROB, CONC_L, PROB_L),
    put_assoc(CID, PROB, CONC_R, PROB_R),
    verify(STRM, PROB_L, FP), 
    verify(STRM, PROB_R, FP) ;

    CH = 'C' -> 
    get_id(STRM, PID), 
    get_term(STRM, TERM), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    cb(TERM, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N),
    verify(STRM, PROB_N, FP) ;

    CH = 'D' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    db(FP, PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N),
    FP_N is FP + 1,
    verify(STRM, PROB_N, FP_N) ;

    CH = 'F' -> 
    get_form(STRM, FORM), 
    get_id(STRM, CID), 
    put_assoc(CID, PROB, (- FORM), PROB_N),
    verify(STRM, PROB_N, FP),
    put_assoc(CID, PROB, (+ FORM), PROB_P),
    verify(STRM, PROB_P, FP) ;

    CH = 'S' -> 
    get_id(STRM, PID), 
    get_id(STRM, CID), 
    get_assoc(PID, PROB, PREM),
    sb(PREM, CONC), 
    put_assoc(CID, PROB, CONC, PROB_N),
    verify(STRM, PROB_N, FP) ;

    CH = 'T' -> 
    get_sf(STRM, SF), 
    get_atoms(STRM, _), 
    get_id(STRM, CID), 
    put_assoc(CID, PROB, SF, PROB_N),
    verify(STRM, PROB_N, FP) ;
    
    CH = 'W' -> 
    get_id(STRM, PID), 
    del_assoc(PID, PROB, _, PROB_N),
    verify(STRM, PROB_N, FP) ;

    CH = 'X' -> 
    get_id(STRM, PID), 
    get_id(STRM, NID), 
    get_assoc(PID, PROB, + FORM_P),
    get_assoc(NID, PROB, - FORM_N),
    FORM_P == FORM_N
  ).
  