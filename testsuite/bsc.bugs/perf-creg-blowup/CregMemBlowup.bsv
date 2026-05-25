// Regression test for the AVerilog.ds7 quadratic.
//
// Many CRegs *and* significant per-rule arithmetic.  After AOpt the
// number of local defs surviving to AVerilog is high; without the
// isADefFromMap fix the verilog phase becomes quadratic in the number
// of defs and balloons.
package CregMemBlowup;

import Vector::*;

typedef 256 NCregs;
typedef 1024 NShadow;     // = NCregs * nports
Integer nports = 4;
typedef 32 Width;

function Bit#(n) churn(Bit#(n) x, Bit#(n) y);
   Bit#(n) a0 = x + y;
   Bit#(n) a1 = a0 ^ (x << 1);
   Bit#(n) a2 = a1 - (y >> 1);
   Bit#(n) a3 = a2 | (x & y);
   Bit#(n) a4 = a3 + (a0 ^ a1);
   Bit#(n) a5 = a4 ^ (a2 - a3);
   Bit#(n) a6 = (a5 << 2) + (a0 >> 2);
   Bit#(n) a7 = a6 - (a1 & a4);
   Bit#(n) a8 = a7 | (a3 ^ a5);
   Bit#(n) a9 = a8 + (a2 - a6);
   return a9 ^ (a0 + a4) - (a5 & a8);
endfunction

(* synthesize *)
module mkCregMemBlowup (Empty);

   Vector#(NShadow, Reg#(Bit#(Width))) shadow <- replicateM(mkReg(0));

   for (Integer i = 0; i < valueOf(NCregs); i = i + 1) begin
      Reg#(Bit#(Width)) cr[nports] <- mkCReg(nports, 0);

      rule feed;
         cr[0] <= shadow[i * nports] + 1;
      endrule

      for (Integer p = 0; p < nports; p = p + 1) begin
         rule rstep;
            Bit#(Width) a = cr[p];
            Bit#(Width) b = shadow[(i + p) % valueOf(NCregs)];
            Bit#(Width) c = shadow[(i + p + 1) % valueOf(NCregs)];
            Bit#(Width) d = shadow[(i + p + 2) % valueOf(NCregs)];
            Bit#(Width) v1 = churn(a, b);
            Bit#(Width) v2 = churn(v1, c);
            Bit#(Width) v3 = churn(v2, d);
            Bit#(Width) v4 = churn(v3, a + b);
            shadow[i * nports + p] <= v4;
         endrule
      end
   end

endmodule

endpackage
