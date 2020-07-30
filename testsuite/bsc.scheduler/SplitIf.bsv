interface Test;
  method Action xfer(Bool sel);
endinterface

(* synthesize *)
module mkSplitIf_Test(Test);
 
  Reg#(Bool)   r1 <- mkReg(True);
  Reg#(Bool)   r2 <- mkReg(False);
  RWire#(Bool) w  <- mkRWire();

  (* descending_urgency = "xfer, toggle1" *)
  rule toggle1;
    r1 <= !r1;
  endrule

  rule toggle2;
    r2 <= !r2;
    w.wset(r2);
  endrule

  method Action xfer(Bool sel) if (w.wget() matches tagged Valid .x);
    if (r1)
    begin
      r1 <= sel;   
      $display("Updating r1 to %b", sel);
    end
    else
    begin
      r2 <= sel;
      $display("Updating r2 to %b", sel);
    end
  endmethod

endmodule

(* synthesize *)
module sysSplitIf();
  
  Reg#(Bool)     dir   <- mkReg(False);
  Reg#(UInt#(4)) count <- mkReg(0);
  Test           test  <- mkSplitIf_Test();

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