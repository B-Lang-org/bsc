import BRAM :: *;
import Latency1Port :: *;
(*synthesize*)
module sysLat122 ();
   let cfg = defaultValue ;
   cfg.latency = 2;
   cfg.outFIFODepth = 2;
   mkLatency1Port (cfg);
endmodule
