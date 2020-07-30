// should trigger G0015 (not always enabled)
// because the bypass wire is not always written
(* synthesize *)
module mkTestENBypassWire(Empty);
  
  Reg#(Bool) toggle <- mkReg(False);
  Reg#(Bit#(32)) counter <- mkReg(0);
  
  Wire#(Bit#(32)) testWire <- mkBypassWire;
  
  rule tick;
    toggle <= !toggle;
    counter <= counter + 1;
  endrule

  rule write(toggle);
    testWire <= counter * counter;
  endrule

  rule display;
    $display("Wire: %h", testWire);
  endrule

endmodule
