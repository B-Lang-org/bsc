package Design;

interface Design_IFC;
   method Action setInputs(Bit#(1) in1, Bit#(1) in2, Bit#(1) in3, Bit#(1) in4);
   method Bit#(8) out();
endinterface: Design_IFC 
          
(* synthesize,
       always_ready ,
       always_enabled
 *)
module mkDesign(Design_IFC);

  Reg#(Bit#(8)) reg_a <- mkRegA(8'b00000000);

  method Action setInputs(in1, in2, in3, in4);
   action
      if ((in1 == 1) && (in2 == 1))
          reg_a <= 8'b00000010;
      else if ((in3 == 1) && (in4 == 0))
          reg_a <= 8'b00100000;
      else
          reg_a <= 8'b00000001;
     

   endaction
   endmethod : setInputs


   method out();
        out = reg_a;
  endmethod: out

endmodule : mkDesign
endpackage: Design
