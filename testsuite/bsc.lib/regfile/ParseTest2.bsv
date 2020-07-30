import RegFile::*;

typedef Bit#(5) Address;
typedef Bit#(12) Data;

(* synthesize *)
module sysParseTest2();

   RegFile#(Address, Data) mem <- mkRegFileFullLoadBin("parse-test.2.bin");

   Reg#(Address) ptr <- mkReg(0);

   rule r;
      $display("%h: %b", ptr, mem.sub(ptr));
      ptr <= ptr + 1;
      if (ptr == maxBound)
	 $finish(0);
   endrule

endmodule

