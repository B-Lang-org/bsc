import FloatingPoint::*;
import StmtFSM::*;
import FShow::*;

function Int #(32) fp64_to_int32 (FP64    x)   = toInt32 (x);
function FP64      int32_to_fp64 (Int #(32) y) = fromInt32 (y);

// Computes the xAT/yAT stuff based on uData [x,y]
(* noinline *)
function Tuple4 #(FP64, Int #(32), FP64, Int #(32)) f_xAT_yAT (FP64 c, Int#(32) sz);
   FP64  nfzAT = ((c < 0.0) ? 0.0 : ((c > int32_to_fp64 (sz - 1)) ? int32_to_fp64 (sz - 1) : c ));
   Int #(32) zAT   = fp64_to_int32 (nfzAT);
   FP64    dzAT  = nfzAT - int32_to_fp64 (zAT);
   Int #(32) nzAT  = ((dzAT > 0.0) ? zAT + 1 : zAT);
   return tuple4 (nfzAT, zAT, dzAT, nzAT);
endfunction

(* synthesize *)
module sysSynth();
   
   Stmt test =
   seq
      delay(10);
      action
	 FP64 c      = 640.0001;
	 Int#(32) sz = 645;
	 FP64 nfzat, dzat;
	 Int#(32) zat, nzat;
	 { nfzat, zat, dzat, nzat } = f_xAT_yAT(c, sz);
	 $display("640.0001,645 = ", fshow(nfzat), fshow(" "), fshow(zat), fshow(" "), fshow(dzat), fshow(" "), fshow(nzat));
      endaction
      action
	 FP64 c      = 640.9001;
	 Int#(32) sz = 640;
	 FP64 nfzat, dzat;
	 Int#(32) zat, nzat;
	 { nfzat, zat, dzat, nzat } = f_xAT_yAT(c, sz);
	 $display("640.9001,640 = ", fshow(nfzat), fshow(" "), fshow(zat), fshow(" "), fshow(dzat), fshow(" "), fshow(nzat));
      endaction
      
      action
	 FP64 c      = 640.9001;
	 Int#(32) sz = 643;
	 FP64 nfzat, dzat;
	 Int#(32) zat, nzat;
	 { nfzat, zat, dzat, nzat } = f_xAT_yAT(c, sz);
	 $display("640.9001,643 = ", fshow(nfzat), fshow(" "), fshow(zat), fshow(" "), fshow(dzat), fshow(" "), fshow(nzat));
      endaction
      
      delay(10);
   endseq;
   
   mkAutoFSM(test);
endmodule
