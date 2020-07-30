interface Ifc#(type a, type b, type c);
    method Bit#(TMin#(TMin#(a,b),c)) m(Bit#(a) x, Bit#(b) y, Bit#(c) z);
endinterface

(* synthesize *)
module sysAddTMin_Multiple (Ifc#(m,n,p));
    method m(x,y,z);
        Bit#(TMin#(m,TMin#(n,p))) v1 = truncate(x);
        Bit#(TMin#(TMin#(m,p),n)) v2 = truncate(y);
        Bit#(TMin#(TMin#(n,p),m)) v3 = truncate(z);
        return (v1 & v2 & v3);
    endmethod
endmodule

