import Vector :: *;

(* synthesize *)
module mkMutEx();

   Vector#(2,Reg#(Bool)) flag <- replicateM(mkReg(True));
   Reg#(Bool)            x    <- mkRegU();

   rule r1 if (flag[0]);
      $display("R1");
      x <= !x;
      flag[0] <= False;
   endrule

// Compiler does not see mutual exclusivity of r1 and r2 with this:
   Bit#(2) prefix = pack(readVReg(flag)) & 2'b01;

// Compiler does see mutual exclusivity of r1 and r2 with this:
//   Bit#(2) prefix = {1'b0,pack(flag[0])};

   rule r2 if (flag[1] && prefix == '0);
      $display("R2");
      x <= !x;
      flag[1] <= False;
   endrule

   rule done if (pack(readVReg(flag)) == '0);
      $finish(0);
   endrule

endmodule
