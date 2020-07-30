typedef union tagged {
  String Value;
  Action Thunk;
  void DoNothing;		       
} AV;

(* synthesize *)
module sysTaggedUnionDynamicAction();

  AV avString = tagged Value "Hello world";
  AV avAction = tagged Thunk 
                   action
                      $display("Goodbye world");
		      $finish(0);
		   endaction;

  Reg#(Bit#(5)) count <- mkReg(0);
 
  Reg#(Bool) switch1 <- mkReg(True);
  Reg#(Bool) switch2 <- mkReg(True);
   
  AV av =  switch1 ? avString : avAction;
  AV av2 = switch2 ? tagged DoNothing : av;
   
  rule test;
    count <= count + 1;
    $display("Count: %0d", count);   
    case(av2) matches
       tagged Thunk .a: a;
       tagged Value .s: $display(s);
    endcase
    switch2 <= !switch2;
    if(!switch2) switch1 <= !switch1;
  endrule

endmodule
 
