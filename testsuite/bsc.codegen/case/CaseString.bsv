(* synthesize *)
module sysCaseString();
   Reg#(Bit#(2)) rg <- mkReg(1);
   rule r;
      String s;
      case (rg)
         0 : s = "zero";
         1 : s = "one";
         2 : s = "two";
         default : s = "three";
      endcase
      $display(s);
   endrule
endmodule
