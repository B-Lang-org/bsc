import Sub::*;

(* synthesize *)
module sysMethodConds_CaseCond ();
   Ifc s <- mkUserSub;

   Reg#(UInt#(2)) idx <- mkReg(0);
   Reg#(Bool) c0 <- mkReg(False);
   Reg#(Bool) c1 <- mkReg(False);
   Reg#(Bool) c2 <- mkReg(False);
   Reg#(Bool) c3 <- mkReg(False);

   function Bool c();
      case (idx)
         0 : return c0;
         1 : return c1;
         2 : return c2;
         default : return c3;
      endcase
   endfunction

   rule r1;
      if (c) begin
         s.am1(0);
	 s.am2;
	 $display("True");
      end
   endrule

endmodule

