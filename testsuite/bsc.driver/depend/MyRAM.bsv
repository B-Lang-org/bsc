import MyClientServer::*;

typedef union tagged {
    adr Read;
    Tuple2#(adr, dta) Write;
} MyRAMreq #(type adr, type dta) deriving (Eq, Bits);

typedef MyServer#(MyRAMreq#(adr, dta), dta) MyRAM #(type adr, type dta);

typedef MyClient#(MyRAMreq#(adr, dta), dta) MyRAMclient #(type adr, type dta);

