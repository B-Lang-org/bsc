import RegFile::*;

(* synthesize *)
module sysWindowsRF();
   
   RegFile#(UInt#(3), UInt#(8)) rf <- mkRegFileFullLoad("windows.hex");
   
   rule r;
      $display("%d", rf.sub(4));
      $finish(0);
   endrule
   
endmodule