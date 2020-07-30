interface Ifc;
   method Bool get();
   method Action act();
endinterface: Ifc

(* synthesize *)
module sysMethodWires(Ifc);

   Reg#(Bool) state <- mkReg(False);
   
   method Bool get() if (state);
      return False;
   endmethod: get

   method Action act();
      state <= False;
   endmethod: act

endmodule

