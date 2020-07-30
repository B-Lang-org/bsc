interface Ifc#(type a, type b);
    method Bit#(TMin#(a,b)) m(Bit#(a) x, Bit#(b) y);
endinterface

(* synthesize *)
module sysAddTMin_Simple (Ifc#(m,n));
    method m(x,y);
        Bit#(TMin#(m,n)) v1 = truncate(x);
        Bit#(TMin#(m,n)) v2 = truncate(y);
        return (v1 & v2);
    endmethod
endmodule

