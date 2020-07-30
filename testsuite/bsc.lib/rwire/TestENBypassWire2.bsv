// should NOT trigger G0015
// because the bypass wire is always written
// note that (so far) I believe a more sophisticated test 
// (e.g. multi-rule) will fail if the BypassWire is inlined
(* synthesize *)
module mkTestENBypassWire2(Empty);
  
  Reg#(Bool) toggle <- mkReg(False);
  Reg#(Bit#(32)) counter <- mkReg(0);
  
  Wire#(Bit#(32)) testWire <- mkBypassWire;
  
  rule tick;
    toggle <= !toggle;
    counter <= counter + 1;
  endrule

  rule write;
    if (toggle)
      testWire <= counter * counter;
    else testWire <= 0;
  endrule

  rule display;
    $display("Wire: %h", testWire);
  endrule

endmodule
