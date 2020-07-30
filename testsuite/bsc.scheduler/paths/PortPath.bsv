(* synthesize *)
module sysPortPath();
   RWire#(void) rw <- mkRWire;
   let x = isValid (rw.wget);

   Ifc s <- mkPortPath_Sub(x);

   rule close_loop;
      if (s.m)
	 rw.wset(?);
   endrule
endmodule

interface Ifc;
   method Bool m();
endinterface

(* synthesize *)
module mkPortPath_Sub#(Bool v) (Ifc);
   // first try, no indirection
   method m = v;
endmodule

