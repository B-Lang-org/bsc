interface PathIfc;
  method Action set(Bool b);   
  method Bool test();
endinterface: PathIfc

(* synthesize *)
module sysPath(PathIfc);

   Reg#(Bool) x <- mkReg(False);
   Wire#(Bool) ok_to_read <- mkDWire(True);

   method Action set(Bool b);
      x <= b;
      ok_to_read <= False;
   endmethod: set
   
   method Bool test() if (ok_to_read);
      return x;
   endmethod: test
   
endmodule: sysPath