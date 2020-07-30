import RegFile::*;

(* synthesize *)
module sysSparseRF(Empty) ;

   RegFile#(UInt#(42), UInt#(8)) rf <- mkRegFileFullLoad("mem2.dat");

   Reg#(UInt#(42)) rd_addr <- mkReg(10290000);
   Reg#(UInt#(42)) wr_addr <- mkReg(0);
   Reg#(UInt#(8)) val <- mkReg(0);
   
   rule incr_val;
      val <= val + 1;
   endrule
   
   rule region_1(wr_addr < 700);
      rf.upd(wr_addr,val);
      wr_addr <= wr_addr + 1;
   endrule
   
   rule jump_1(wr_addr == 700);
      wr_addr <= 10293874;
   endrule

   rule region_2(wr_addr > 700 && wr_addr < 10295000);
      rf.upd(wr_addr,val);
      wr_addr <= wr_addr + 1;
   endrule
   
   rule jump_2(wr_addr == 10295000);
      wr_addr <= 42'h3fffffff123;
   endrule

   rule region_3(pack(wr_addr)[41] != 0);
      rf.upd(wr_addr,val);
      wr_addr <= wr_addr + 1;
   endrule

   rule reader;
      $display("rf[%0d] = %h", rd_addr, rf.sub(rd_addr));
      rd_addr <= rd_addr + 1;
   endrule
   
   rule done (wr_addr == 42'h3ffffffffff);
      $finish(0);
   endrule
   
endmodule


