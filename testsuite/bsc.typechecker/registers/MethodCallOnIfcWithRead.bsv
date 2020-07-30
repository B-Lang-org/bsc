// Test that implicit ._read is not added to variable references
// when another method on that ifc is already being applied.

(* synthesize *)
module sysMethodCallOnIfcWithRead (Empty);
   ChangedReg#(Bit#(8)) cr <- mkChangedReg(0);

   rule r1 (True);
      cr <= cr + 1;
   endrule

   rule r2 (cr.changed);
      $display("Changed!");
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


