/////////////////////////////////////////////////////////////////////////
/* Frame Buffer.
Consists of Two RAMs. 
When you write into one of the rams, you read from the other.
It is used to store the complete frame of a MPEG-4 frame
whose max size can be 396 macroblocks.There are 6 blocks
in 1 macroblock and each block is a 8x8 matrix with 
8 bit coefficients.So when the MCR is reading from
one ram ( called reference frame ) the resulting frame
is written into second ram ( current frame).After processing
one frame the current frame becomes reference frame for the next
frame.
*/

package FrmBuffer;
import RegFile::*;
import ConfigReg::*;

// data and strobe
typedef Tuple3#(Bit#(1), RamAddr_t, RamData_t) DataStrobe;

typedef Bit#(18)  RamAddr_t;
typedef Bit#(8)   RamData_t;

interface FrmBuffer_IFC;
   method Action set_level (Bit#(2) level) ;
   method Action write_d (DataStrobe write_data,Bit#(2) level);
   method Action read_d(Tuple2#(Bit#(1),RamAddr_t) read_data);
   method RamData_t sent_rd_data;
   method Action set_rd_vop (Bit#(1) rd_vop);
   method Bool vop_done;
   method RamData_t vop_data;
   method Bool vop_rd_done;
   method Bit#(1) mb_done;
   method Action set_disable_mb_done (Bit#(1) disable_mb_done);
endinterface : FrmBuffer_IFC

typedef enum {StateA, StateB} States
deriving (Eq, Bits);

typedef struct 
{ States    memBank;
 RamAddr_t addR;
 } FrmCnt
deriving (Eq, Bits);

(* synthesize ,
 CLK = "clk",
 RST_N = "reset"
 *)
module mkFrmBuffer (FrmBuffer_IFC);

   // instantiate both RAMS
   RegFile#(RamAddr_t,RamData_t) ram1();
   mkRegFile #(0,152063) the_ram1 (ram1);
   RegFile#(RamAddr_t,RamData_t) ram2();
   mkRegFile #(0,152063) the_ram2 (ram2);
   
   Reg#(FrmCnt) write_counter() ;
   mkConfigReg#(FrmCnt {memBank : StateA, addR: 0}) i_write_counter(write_counter);
   
   RWire#(DataStrobe) wr_data();
   mkRWire i_wr_data(wr_data) ;
   
   RWire#(Tuple2#(Bit#(1),RamAddr_t)) rd_data();
   mkRWire i_rd_data(rd_data) ;
   
   Reg#(RamData_t) out_data() ;
   mkReg#(0) i_out_data(out_data) ;

   Reg#(RamAddr_t) frm_addr() ;
   mkReg#(0) i_frm_addr(frm_addr) ;

   Reg#(Bool)    vop_done_reg() ;
   mkReg#(False) i_vop_done_reg(vop_done_reg) ;

   Reg#(Bool)    vop_rd_done_reg() ;
   mkReg#(False) i_vop_rd_done_reg(vop_rd_done_reg) ;

   Reg#(Bit#(1)) mb_done_reg() ;
   mkReg#(0)     i_mb_done_reg(mb_done_reg) ;

   Reg#(Bit#(3)) block_cnt() ;
   mkReg#(0)     i_block_cnt(block_cnt) ;

   Reg#(RamData_t) vop_data_reg() ;
   mkReg#(0) i_vop_data_reg(vop_data_reg) ;

   RWire#(Bit#(2))   level();
   mkRWire           t_level(level);

   RWire#(Bit#(1))   rd_vop();
   mkRWire           t_rd_vop(rd_vop);

   RWire#(Bit#(1))   disable_mb_done();
   mkRWire           t_disable_mb_done(disable_mb_done);

   Bit#(2)  tmp_level = validValue(level.wget);
   RamAddr_t tmp_frmsize   = (tmp_level[1] == 1) ? 152064 :  38016 ;
   

   rule writeRAMA (write_counter.memBank == StateA &&& wr_data.wget matches tagged Valid {.s,.addr,.dta});
      if (s == 1)
	 begin
            ram1.upd(addr,dta);
	    //$display("Writing first buffer data = %h addr = %d",dta,addr);
	 end
   endrule
   
   rule writeRAMB (write_counter.memBank == StateB &&& wr_data.wget matches tagged Valid {.s,.addr,.dta});
      if (s == 1)
	 begin
            ram2.upd(addr,dta);
	    //$display("Writing Second buffer data = %h addr = %d",dta,addr);
	 end
   endrule
   
   rule alwaysRead (write_counter.memBank == StateB &&& rd_data.wget matches tagged Valid {.rd_addr,.addr});
      if (rd_addr == 1)
         out_data <= ram1.sub(addr);
   endrule
   
   rule alwaysRead2 (write_counter.memBank == StateA &&& rd_data.wget matches tagged Valid {.rd_addr,.addr});
      if (rd_addr == 1)
         out_data <= ram2.sub(addr);
   endrule

   rule read_vop_data1 (rd_vop.wget == Just(1) && write_counter.memBank == StateB);
      if (frm_addr == tmp_frmsize)
	 begin
	    vop_rd_done_reg <= True;
	    frm_addr <= 0;
	    vop_data_reg <= 0;
	 end
      else
	 begin
	    vop_rd_done_reg <= False;
	    frm_addr <= frm_addr + 1;
	    let tmp_vop_data_reg = ram1.sub(frm_addr);
	    vop_data_reg <= tmp_vop_data_reg;
	    //$display("Reading First buffer data = %h addr = %d",tmp_vop_data_reg,frm_addr);
	 end
   endrule

   rule read_vop_data2 (rd_vop.wget == Just(1) && write_counter.memBank == StateA);
      if (frm_addr == tmp_frmsize)
	 begin
	    vop_rd_done_reg <= True;
	    frm_addr <= 0;
	    vop_data_reg <= 0;
	 end
      else
	 begin
	    vop_rd_done_reg <= False;
	    frm_addr <= frm_addr + 1;
	    let tmp_vop_data_reg = ram2.sub(frm_addr);
	    vop_data_reg <= tmp_vop_data_reg;
	    //$display("Reading Second buffer data = %h addr = %d",tmp_vop_data_reg,frm_addr);
	 end
   endrule

   rule assign_mb_done_reg;
      if (disable_mb_done.wget == Just(1))
	 mb_done_reg <= 1'b0;
      else if (write_counter.addR == tmp_frmsize)
	 begin
	    mb_done_reg <= 1'b0;
	    block_cnt <= 0;
	 end
      else if (write_counter.addR[5:0] == 63) // one MB has been written into buffer
	 begin
	    if (block_cnt == 5)
	       begin
	          mb_done_reg <= 1'b1;
		  block_cnt <= 0;
	       end
	    else
	       begin
		  block_cnt <= block_cnt + 1;
	       end
	 end
   endrule

   method Action write_d (a,b);
      RamAddr_t frmsize   = (b[1] == 1) ? 152064 :  38016 ;
      wr_data.wset (a) ;
      if (write_counter.addR == frmsize)
         begin
            write_counter <= FrmCnt { memBank: (write_counter.memBank==StateA?
                                                StateB:StateA),
                                     addR:0};
	    vop_done_reg <= True;
         end
      else if ( tpl_1(a) == 1)
         begin
            write_counter <= FrmCnt { memBank: write_counter.memBank, addR:write_counter.addR+1};
	    vop_done_reg <= False;
         end
      else if (vop_done_reg)
	 vop_done_reg <= False;

   endmethod : write_d 

   method Action read_d (a);
      rd_data.wset(a) ;
   endmethod : read_d 

   method RamData_t sent_rd_data;
      sent_rd_data = out_data; 
   endmethod : sent_rd_data

   method set_level (x);
      action
	 level.wset(x);
      endaction
   endmethod : set_level

   method set_rd_vop (x);
      action
	 rd_vop.wset(x);
      endaction
   endmethod : set_rd_vop

   method vop_done;
      vop_done = vop_done_reg; 
   endmethod : vop_done

   method RamData_t vop_data;
      vop_data = vop_data_reg; 
   endmethod : vop_data

   method vop_rd_done;
      vop_rd_done = vop_rd_done_reg; 
   endmethod : vop_rd_done

   method mb_done;
      mb_done = mb_done_reg; 
   endmethod : mb_done

   method set_disable_mb_done (x);
      action
	 disable_mb_done.wset(x);
      endaction
   endmethod : set_disable_mb_done

endmodule: mkFrmBuffer

endpackage: FrmBuffer
