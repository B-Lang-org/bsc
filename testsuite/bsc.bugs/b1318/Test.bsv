
(* always_ready, always_enabled *)
interface InSubIfc;
   method Bool data();
endinterface

interface InIfc;
   interface InSubIfc in;
endinterface

interface OutIfc;
   method Bool out_data();
endinterface

(* synthesize *)
module mkTest#(InIfc m)(OutIfc);

   Wire#(Bool) data_wire <- mkDWire(?);

   rule add_label;
      data_wire <= m.in.data;
   endrule
   
   method out_data();
      return data_wire;
   endmethod

endmodule

