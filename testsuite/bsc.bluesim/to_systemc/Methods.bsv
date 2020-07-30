interface MethodIfc;
  method ActionValue#(Bool) toggle();   
  method Bool get(Bool unused);
endinterface: MethodIfc

(* synthesize *)
module sysMethods(MethodIfc);

   Reg#(Bool) x <- mkReg(False);

   method ActionValue#(Bool) toggle();
      x <= !x;
      return x;
   endmethod: toggle
   
   method Bool get(Bool unused);
      return x;
   endmethod: get
   
endmodule: sysMethods