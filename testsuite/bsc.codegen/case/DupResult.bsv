
(* synthesize *)
module sysDupResult ();

   Reg#(Bit#(3)) r_idx <- mkReg(0);
   Reg#(Bit#(32)) r_vec <- mkReg(32'hAABBCCDD);

   rule r;
      Bit#(8) tmp;
      case (r_idx)
         0: tmp = r_vec[7:0];
         1: tmp = r_vec[15:8];
         2: tmp = r_vec[7:0];
         3: tmp = r_vec[23:16];
         4: tmp = r_vec[23:16];
         5: tmp = r_vec[31:24]; // test duplicate of the default, too
         6: tmp = r_vec[7:0];
         default: tmp = r_vec[31:24];
      endcase
      $displayh(tmp);

      r_idx <= r_idx + 1;
      if (r_idx == 7)
         $finish(0);
   endrule

endmodule

