
(* synthesize *)
module sysIfElseCase_Inline ();

   Reg#(Bit#(2)) r_idx <- mkReg(0);
   Reg#(Bit#(32)) r_vec <- mkReg(32'hAABBCCDD);

   rule r;
      Bit#(8) tmp;
      if (r_idx == 0)
         tmp = 0;
      else begin
         case (r_idx)
            0: tmp = r_vec[7:0];
            1: tmp = r_vec[15:8];
            2: tmp = r_vec[23:16];
            default: tmp = r_vec[31:24];
         endcase
      end
      $displayh(tmp);

      r_idx <= r_idx + 1;
      if (r_idx == 3)
         $finish(0);
   endrule

endmodule

