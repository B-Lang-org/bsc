(* synthesize *)
module mkRenameTest();
  Reg#(UInt#(8)) count <- mkReg(0);

  rule increment (count < 100);
    count <= count + 1;
  endrule
endmodule
