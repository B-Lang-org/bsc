
(* synthesize *)
module sysBug1591();

   rule r;
      Bit#(0) data = ?;
      $display("%x", data);
   endrule

endmodule
