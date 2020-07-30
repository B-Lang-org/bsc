import BRAM :: *;
import Latency1Port :: *;
(*synthesize*)
module sysLat124 ();
   let cfg = defaultValue ;
   cfg.latency = 2;
   cfg.outFIFODepth = 4;
   mkLatency1Port (cfg);
endmodule
