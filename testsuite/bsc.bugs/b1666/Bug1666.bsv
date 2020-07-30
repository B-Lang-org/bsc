(* synthesize *)
module mkBug1666Reg #(parameter Bit#(8) p) (Reg#(Bit#(6)));
   Reg#(Bit#(6)) rg <- mkReg( (p + 1)[7:2] );
   return rg;
endmodule

(* synthesize *)
module sysBug1666 ();

   Reg#(Bit#(6)) rg <- mkBug1666Reg(8'b10101010);

   Reg#(Bool) done <- mkReg(False);

   rule do_test (!done);
      $display("rg = %h", rg);
      done <= True;
   endrule

   rule do_finish (done);
      $finish(0);
   endrule

endmodule
