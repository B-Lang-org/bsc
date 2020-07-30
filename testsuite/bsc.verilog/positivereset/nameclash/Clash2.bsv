interface Ifc;
   method Int#(2) foo;
   method Action bar;
endinterface


(*synthesize*)
module sysClash2 (Ifc);
endmodule
