
typedef UInt#(14) I;


(*synthesize, options ="-elab"*)
module sysTestRW ();
   RWire#(I) rw <- mkRWire;
   PulseWire pw <- mkPulseWire;
   Wire#(I) ww <- mkDWire(17);
endmodule

