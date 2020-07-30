package Any;
import ClientServer::*;

typedef Server#(RAMreq#(adr, dta), dta) RM #(type adr, type dta);

typedef union tagged { adr Read; Tuple2#(adr, dta) Write; } RAMreq #(type adr, type dta) deriving (Eq, Bits);
endpackage
