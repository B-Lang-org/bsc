import Probe::*;

// uses same interface as a wire
module mkProbeWire( Wire#(tp) ) provisos (Bits#(tp,sizetp));
   Wire#(tp)  wr  <- mkWire;
   Probe#(tp) prb <- mkProbe;   // probe forces this wire to stick around!
   
   method Action _write( tp d );
      wr  <= d;
      prb <= d;
   endmethod

   method tp _read();
      return wr;
   endmethod

endmodule
