(* synthesize *)
module mkSplitFalse();

  Reg#(Bool) a <- mkReg(False);
  Reg#(Bool) b <- mkReg(False);
  Reg#(UInt#(17)) c <- mkReg(0);
  Reg#(UInt#(15)) d <- mkReg(0);

  rule test;
    (* split *)
    action
      if(a) c <= 0;
      else d <= 5;
      if(a) b <= True;
      else c <= 17;
    endaction
  endrule

endmodule

