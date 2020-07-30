interface Ifc;
   method Action m1();
   (* always_enabled *)
   method Action m2();
   method Bool m3();
endinterface

(* synthesize *)
module sysTest_RdyEn_Path(Ifc);
   PulseWire pw1 <- mkPulseWire;
   PulseWire pw2 <- mkPulseWire;

   method Action m1();
      pw1.send;
   endmethod

   method Action m2() if (pw1);
      pw2.send;
   endmethod

   method m3 = pw2;
endmodule
