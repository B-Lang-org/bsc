import Vector::*;

interface ClockIfc;
    interface Clock clk_out;
endinterface

interface Ifc;
    interface Vector#(4,ClockIfc) clks_out;
endinterface

(* synthesize *)
module sysVecClock #(Vector#(4,Clock) clks_in) (Ifc);
    Vector#(4,ClockIfc) outs = ?;
    for (Integer i=0; i<4; i=i+1) begin
	outs[i] = interface ClockIfc;
	              interface clk_out = clks_in[i];
                  endinterface;
    end
    interface clks_out = outs;
endmodule

/* This doesn't work :(

interface Ifc;
    interface Vector#(4,Clock) clks_out;
endinterface

module sysVecClock #(Vector#(4,Clock) clks_in) (Ifc);
   interface clks_out = clks_in;
endmodule
*/
