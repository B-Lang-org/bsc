interface Ifc;
 (* prefix = "p1" *)
 interface SubIfc s;
endinterface

interface SubIfc;
 (* prefix = "p2" *)
 interface Clock c;
endinterface

(* synthesize *)
module mkClock (Ifc);
    Clock clk <- exposeCurrentClock;
    interface SubIfc s;
      interface c = clk;
    endinterface
endmodule
