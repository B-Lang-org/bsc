
// a subfunction which requires TAdd

function Bit#(TAdd#(x,y)) fnSub(Bit#(x) v1, Bit#(y) v2);
   return {v1, v2};
endfunction

// a calling functiont that uses Add instead

function Bit#(n) fnTop(Bit#(x) v1, Bit#(y) v2)
 provisos(Add#(x, y, n));
   return fnSub(v1, v2);
endfunction

(* synthesize *)
module sysNumEq_TwoTAdd (Reg#(Bit#(16)));
   Reg#(Bit#(8)) r1 <- mkRegU;
   Reg#(Bit#(8)) r2 <- mkRegU;

   method _read() = fnTop(r1,r2);

   method Action _write(Bit#(16) x);
      r1 <= x[15:8];
      r2 <= x[7:0];
   endmethod
endmodule
