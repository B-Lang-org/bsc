
function Bool fn(Bit#(nw) w, Bit#(nx) x, Bit#(ny) y, Bit#(nz) z)
 provisos (Add#(nw,nx,sum), Add#(ny,nz,sum));
   Bit#(TAdd#(nw,nx)) v1 = {w,x};
   Bit#(TAdd#(ny,nz)) v2 = {y,z};
   return (v1 == v2);
endfunction

(* synthesize *)
module sysNumEq_TwoTAdd (Reg#(Bit#(8)));
   Reg#(Bit#(8)) r1 <- mkRegU;
   Reg#(Bit#(8)) r2 <- mkRegU;
   Reg#(Bit#(8)) r3 <- mkRegU;
   Reg#(Bit#(8)) r4 <- mkRegU;

   method _read() = fn(r1,r2,r3,r4) ? (r1 + r2) : (r3 + r4);

   method Action _write(Bit#(8) x);
      r1 <= x;
      r2 <= x;
      r3 <= x;
      r4 <= x;
   endmethod
endmodule
