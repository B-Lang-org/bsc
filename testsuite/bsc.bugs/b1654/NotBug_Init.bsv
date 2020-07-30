interface Ifc;
   method ActionValue#(Bit#(8)) res();
endinterface

(* synthesize *)
module mkBug(Ifc);
   method ActionValue#(Bit#(8)) res();
      Bit#(8) r = 'b11001100;
      for (Integer i=0; i<8; i=i+1)
         r[i] = 0;
      return r;
   endmethod
endmodule

