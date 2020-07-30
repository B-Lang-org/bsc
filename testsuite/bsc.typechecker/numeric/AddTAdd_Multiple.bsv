interface Ifc#(type a, type b, type c);
    method Bit#(TAdd#(TAdd#(a,b),c)) m(Bit#(a) x, Bit#(b) y, Bit#(c) z);
endinterface

(* synthesize *)
module sysAddTAdd_Multiple (Ifc#(m,n,p));
    method m(x,y,z);
        Bit#(TAdd#(m,TAdd#(n,p))) v1 = zeroExtend(x);
        Bit#(TAdd#(TAdd#(n,p),m)) v2 = zeroExtend(y);
        Bit#(TAdd#(TAdd#(m,p),n)) v3 = zeroExtend(z);
        return (v1 & v2 & v3);
    endmethod
endmodule

