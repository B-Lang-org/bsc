import BRAM :: *;
import Latency1Port :: *;
(*synthesize*)
module sysLat112 ();
   let cfg = defaultValue ;
   cfg.latency = 1;
   cfg.outFIFODepth = 2;
   mkLatency1Port (cfg);
endmodule
