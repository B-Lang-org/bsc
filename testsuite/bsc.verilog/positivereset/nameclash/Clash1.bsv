interface Ifc;
   method Int#(2) foo;
   method Action bar;
endinterface


//(* reset_prefix = "foo"*)
(*synthesize*)
module sysClash1 (Ifc);
endmodule
