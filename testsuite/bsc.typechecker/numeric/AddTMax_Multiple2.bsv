interface Ifc#(type a, type b, type c);
    method Bit#(TMax#(TMax#(a,b),c)) m(Bit#(a) x, Bit#(b) y, Bit#(c) z);
endinterface

(* synthesize *)
module sysAddTMax_Multiple (Ifc#(m,n,p));
    method m(x,y,z);
        Bit#(TMax#(m,TMax#(n,p))) v1 = zeroExtend(x);
        Bit#(TMax#(TMax#(m,p),n)) v2 = zeroExtend(y);
        Bit#(TMax#(TMax#(n,p),m)) v3 = zeroExtend(z);
        return (v1 & v2 & v3);
    endmethod
endmodule

