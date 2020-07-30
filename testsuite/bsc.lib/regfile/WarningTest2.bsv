
import RegFile::*;

(* synthesize *)
module sysWarningTest2();

   Bit#(3) start_addr = 0;
   Bit#(3) end_addr = 7;

   RegFile#(Bit#(3),Bit#(32)) regMem 
       <- mkRegFileWCFLoad ("warning-test.2.bin", start_addr, end_addr);

   Reg#(Bit#(3)) ptr <- mkReg(start_addr);

   rule rdisp;
      $display("regMem[%h] = %h", ptr, regMem.sub(ptr));
      ptr <= ptr + 1;
      if (ptr == end_addr)
	 $finish(0);
   endrule

endmodule

