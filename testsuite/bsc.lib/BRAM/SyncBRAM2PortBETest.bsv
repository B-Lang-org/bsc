import BRAM         :: *;
import Clocks       :: *;
import DefaultValue :: *;
import LFSR         :: *;

(* synthesize *)
module sysSyncBRAM2PortBETest();

   let rd_clk <- mkAbsoluteClock(1, 8);
   let rd_rst <- mkAsyncResetFromCR(3, rd_clk);

   let wr_clk <- mkAbsoluteClock(4, 13);
   let wr_rst <- mkAsyncResetFromCR(3, wr_clk);

   BRAM_Configure cfg = defaultValue();

   BRAM2PortBE#(UInt#(12),Bit#(16),2) bram_a <- mkSyncBRAM2ServerBE(cfg, wr_clk, wr_rst, rd_clk, rd_rst);

   BRAM2Port#(UInt#(12),Bit#(8)) bram_b0 <- mkSyncBRAM2Server(cfg, wr_clk, wr_rst, rd_clk, rd_rst);
   BRAM2Port#(UInt#(12),Bit#(8)) bram_b1 <- mkSyncBRAM2Server(cfg, wr_clk, wr_rst, rd_clk, rd_rst);


   LFSR#(Bit#(32)) wr_lfsr <- mkLFSR_32(clocked_by wr_clk, reset_by wr_rst);
   Reg#(Bool) wr_seeded <- mkReg(False, clocked_by wr_clk, reset_by wr_rst);

   LFSR#(Bit#(16)) rd_lfsr <- mkLFSR_16(clocked_by rd_clk, reset_by rd_rst);
   Reg#(Bool) rd_seeded <- mkReg(False, clocked_by rd_clk, reset_by rd_rst);

   rule seed_wr if (!wr_seeded);
      wr_lfsr.seed(32'hac671c3b);
      wr_seeded <= True;
   endrule

   rule seed_rd if (!rd_seeded);
      rd_lfsr.seed(16'h72b6);
      rd_seeded <= True;
   endrule

   rule do_write if (wr_seeded);
      Bit#(32) r = wr_lfsr.value();
      wr_lfsr.next();
      Bit#(2)   we   = r[17:16];
      UInt#(12) addr = unpack(r[29:18]);
      Bit#(16)  val  = r[15:0];
      if (we != '0) begin
         // make request to bram_a with 2 byte enables
         BRAMRequestBE#(UInt#(12),Bit#(16),2) req_a = defaultValue();
         req_a.writeen = we;
         req_a.address = addr;
         req_a.datain  = val;
         req_a.responseOnWrite = False;
         bram_a.portA.request.put(req_a);
         // split the same request across bram_b0 and bram_b1 without byte enables
         if (we[0] != 0) begin
            BRAMRequest#(UInt#(12),Bit#(8)) req_b0 = defaultValue();
            req_b0.write   = True;
            req_b0.address = addr;
            req_b0.datain  = val[7:0];
            req_b0.responseOnWrite = False;
            bram_b0.portA.request.put(req_b0);
         end
         if (we[1] != 0) begin
            BRAMRequest#(UInt#(12),Bit#(8)) req_b1 = defaultValue();
            req_b1.write   = True;
            req_b1.address = addr;
            req_b1.datain  = val[15:8];
            req_b1.responseOnWrite = False;
            bram_b1.portA.request.put(req_b1);
         end
      end
   endrule

   rule do_read if (rd_seeded);
      Bit#(16) r = rd_lfsr.value();
      rd_lfsr.next();
      UInt#(12) addr = unpack(r[11:0]);
      // make request to bram_a
      BRAMRequestBE#(UInt#(12),Bit#(16),2) req_a = defaultValue();
      req_a.writeen = '0;
      req_a.address = addr;
      req_a.datain  = ?;
      req_a.responseOnWrite = False;
      bram_a.portB.request.put(req_a);
      // request the same address from bram_b0 and bram_b1
      BRAMRequest#(UInt#(12),Bit#(8)) req_b0 = defaultValue();
      req_b0.write   = False;
      req_b0.address = addr;
      req_b0.datain  = ?;
      req_b0.responseOnWrite = False;
      bram_b0.portB.request.put(req_b0);
      BRAMRequest#(UInt#(12),Bit#(8)) req_b1 = defaultValue();
      req_b1.write   = False;
      req_b1.address = addr;
      req_b1.datain  = ?;
      req_b1.responseOnWrite = False;
      bram_b1.portB.request.put(req_b1);
   endrule

   rule check_response;
      Bit#(16) resp_a  <- bram_a.portB.response.get();
      Bit#(8)  resp_b0 <- bram_b0.portB.response.get();
      Bit#(8)  resp_b1 <- bram_b1.portB.response.get();
      if (resp_a != {resp_b1,resp_b0})
         $display("%0t: Mismatch %x vs {%x,%x}", $time(), resp_a, resp_b1, resp_b0);
   endrule

   rule done;
      let t <- $time();
      if (t > 100000)
         $finish(0);
   endrule

endmodule
