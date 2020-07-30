interface Bypass; 
  method Action send(Bit#(16) data); 
  method Bit#(16) receive;
endinterface

(* 
synthesize, 
always_ready,
always_enabled
*)
module mkTestBypassWire(Bypass);
  
  Wire#(Bit#(16)) myWire <- mkBypassWire;
  
  method Action send(data);
    myWire <= data;
  endmethod

  method receive = myWire;

endmodule

(* synthesize *)
module sysTestBypassWire(Empty);

  Reg#(Bit#(3)) counter <- mkReg(0);

  Bypass bypass <- mkTestBypassWire;

  rule count;
    counter <= counter + 1;
  endrule

  rule bypass_high(counter > 4);
    bypass.send(16'hFFFF);
  endrule
  
  rule bypass_low(counter < 4);
    bypass.send(zeroExtend(counter));
  endrule

  rule bypass4(counter == 4);
    bypass.send(16'hBEEF);
  endrule

  (* no_implicit_conditions, fire_when_enabled *)
  rule display_bypass;
    $display("Bypass value: %h Counter: %0d", bypass.receive, counter);
    if(counter == 7) $finish(0);
  endrule

endmodule


 
    
  
