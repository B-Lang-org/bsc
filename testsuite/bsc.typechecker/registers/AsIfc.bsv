// Test the "asIfc" primitive

(* synthesize *)
module sysAsIfc ();
   ChangedReg#(Bool) cr <- mkChangedReg(False);

   rule r;
      let x = asIfc(cr);
      x <= True;
   endrule
 endmodule

// ----------

interface ChangedReg#(type a_type);
   method Action _write(a_type x);
   method a_type _read();
   method Bool changed();
endinterface

module mkChangedReg#(a init_val) (ChangedReg#(a))
   provisos(Bits#(a,sizeOfa));

   Reg#(a) r <- mkReg(init_val);
   RWire#(void) w <- mkRWire;

   method _read = r;
   method Action _write(a x);
      r <= x;
      w.wset(?);
   endmethod
   method changed = isValid(w.wget);

endmodule

