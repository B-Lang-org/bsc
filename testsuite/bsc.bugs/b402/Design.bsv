package Design;

interface Design_IFC;

    method Bit#(2) out(Bit#(2) indata, Bit#(1) sel);

endinterface

(*     synthesize,
       always_ready ,
       always_enabled ,
       CLK = "clk",
       RST_N = "reset"
 *)

module mkDesign(Design_IFC);

method Bit#(2) out(indata,sel);

  Bit#(2) result;
  result[1]  = (sel == 1'b1) ? indata[1:1] : indata[0:0];
  result[0]  = (sel == 1'b1) ? indata[0:0] : indata[1:1];

out = result;

endmethod

endmodule

endpackage
