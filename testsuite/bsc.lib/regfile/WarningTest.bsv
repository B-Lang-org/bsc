
import RegFile::*;

(* synthesize *)
module sysWarningTest();

   Bit#(5) start_addr = 1;
   Bit#(5) end_addr = 20;

   RegFile#(Bit#(5),Bit#(32)) regMem 
       <- mkRegFileWCFLoad ("warning-test.bin", start_addr, end_addr);

   Reg#(Bit#(5)) ptr <- mkReg(start_addr);

   rule rdisp;
      $display("regMem[%h] = %h", ptr, regMem.sub(ptr));
      ptr <= ptr + 1;
      if (ptr == end_addr)
	 $finish(0);
   endrule

endmodule

