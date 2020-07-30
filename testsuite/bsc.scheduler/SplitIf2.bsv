interface Test;
  method Action xfer(Bool sel);
endinterface

(* synthesize *)
module mkSplitIf2_Test(Test);
 
  Reg#(Bool)   r1 <- mkReg(True);
  Reg#(Bool)   r2 <- mkReg(False);
  RWire#(Bool) w  <- mkRWire();

  rule toggle1;
    r1 <= !r1;
  endrule

  rule toggle2;
    r2 <= !r2;
    w.wset(r2);
  endrule

  method Action xfer(Bool sel) if (w.wget() matches tagged Valid .x);
    if (sel)
    begin
      r1 <= r2;   
      $display("Updating r1 to %b", r2);
    end
    else
    begin
      r2 <= r1;
      $display("Updating r2 to %b", r1);
    end
  endmethod

endmodule

(* synthesize *)
module sysSplitIf2();
  
  Reg#(Bool)     dir   <- mkReg(False);
  Reg#(UInt#(4)) count <- mkReg(0);
  Test           test  <- mkSplitIf2_Test();

  rule toggleDir;
    dir <= !dir;
  endrule

  rule r;
    test.xfer(dir);
  endrule

  rule incr;
    count <= count + 1;
  endrule
  
  rule done (count == 15);
    $finish(0);
  endrule

endmodule