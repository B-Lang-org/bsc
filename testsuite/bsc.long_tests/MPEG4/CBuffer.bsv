/////////////////////////////////////////////////////////////////////////
/* Frame Buffer.
   Consists of Two RAMs. 
   When you write into one of the rams, you read from the other.
*/

package CBuffer;

import Registers::*;
import RegFile::*;
import ConfigReg::*;

typedef Bit#(6)  RamAddr_t;
typedef Bit#(12) RamData_t;

interface CBuffer_IFC;
   method Action write_d (Tuple3#(Bit#(1),RamAddr_t,RamData_t) write_data);
   method Action read_d(Tuple2#(Bit#(1),RamAddr_t) read_data);
   method Action clear_d(Bit#(1) cl);
   method Action sent_output_data(Bit#(1) sent);
   method Bool busy;
   method RamData_t wr_data_read;
   // signals related to output buffer to be sent to IDCT
   method RamData_t data_out;
   method Bit#(1)   data_valid;
endinterface : CBuffer_IFC

typedef enum {StateA, StateB} States
    deriving (Eq, Bits);

typedef struct 
    { States    x;
      RamAddr_t y;
    } BlkCnt
    deriving (Eq, Bits);

(* synthesize ,
   CLK = "clk",
   RST_N = "reset"
*)
module mkCBuffer (CBuffer_IFC);

   // instantiate both RAMS
   MYRegFile ram1 <- mkRS;
   MYRegFile ram2 <- mkRS;
  
   Reg#(BlkCnt) write_counter() ;
   mkConfigReg#(BlkCnt {x : StateA, y: 0}) i_write_counter(write_counter);
   
   Reg#(BlkCnt) read_counter() ;
   mkConfigReg#(BlkCnt {x : StateB, y: 0}) i_read_counter(read_counter);
   
   RWire#(Tuple3#(Bit#(1),RamAddr_t,RamData_t)) wr_data();
   mkRWire i_wr_data(wr_data) ;
   
   RWire#(Tuple2#(Bit#(1),RamAddr_t)) rd_data();
   mkRWire i_rd_data(rd_data) ;
   
   RWire#(void) clear_reg();
   mkRWire i_clear_reg(clear_reg) ;
   
   RWire#(Bit#(1)) sent_reg();
   mkRWire i_sent_reg(sent_reg) ;
   
   Reg#(RamData_t) data_read_reg() ;
   mkReg#(0) i_data_read_reg(data_read_reg) ;

   Reg#(RamData_t) out_data() ;
   mkReg#(0) i_out_data(out_data) ;

   Reg#(Bit#(1)) valid() ;
   mkReg#(0) i_valid(valid) ;

   Reg#(Bool)    rd_mem_flag() ;
   mkReg#(False) i_rd_mem_flag(rd_mem_flag) ;

  rule always_fire(sent_reg.wget == Just(1));
       write_counter <= BlkCnt { x: (write_counter.x==StateA?
                                     StateB:StateA),
                                  y:0};
       read_counter <= BlkCnt { x: (read_counter.x==StateA?
                                     StateB:StateA),
                                  y:0};
	  rd_mem_flag <= True;
  endrule

   rule writeRAMA ((write_counter.x == StateA) && (clear_reg.wget == Nothing));
      if (wr_data.wget matches tagged Just {.s,.addr,.dta} )
        begin
		  if (s == 1)
		    begin
                       ram1.upd(addr,dta);
	               //$display("writing ram1 addr = %d data = %h",addr,dta);
		    end
        end 
   endrule

   rule writeRAMB ((write_counter.x == StateB) && (clear_reg.wget == Nothing));
      if (wr_data.wget matches tagged Just {.s,.addr,.dta} )
        begin
		  if (s == 1)
		    begin
                       ram2.upd(addr,dta);
	               //$display("writing ram2 addr = %d data = %h",addr,dta);
		    end
        end 
   endrule

   rule clearRAMAB (clear_reg.wget != Nothing);
     if (write_counter.x == StateA)
       ram1.clear(1'b1);
	 else
       ram2.clear(1'b1);
   endrule

   rule readRAMA (write_counter.x == StateA) ;
      if (rd_data.wget matches tagged Just {.s,.addr} )
	    begin
	       if (s == 1) begin
                  //out_data <= ram1.sub1(addr);
                  RamData_t tmp_out_data = ram1.sub1(addr);
		  //$display("reading ram1 addr = %d data = %h",addr,tmp_out_data);
                  out_data <= tmp_out_data;
	       end
	    end
   endrule
   
   rule readRAMB (write_counter.x == StateB) ;
      if (rd_data.wget matches tagged Just {.s,.addr} )
	    begin
	       if (s == 1) begin
                  //out_data <= ram2.sub1(addr);
                  RamData_t tmp_out_data = ram2.sub1(addr);
		  //$display("reading ram2 addr = %d data = %h",addr,tmp_out_data);
                  out_data <= tmp_out_data;
	       end
	    end
   endrule

   //rule alwaysreadRAMA ((write_counter.x == StateB) && rd_mem_flag);
   rule alwaysreadRAMA ((read_counter.x == StateA) && rd_mem_flag);
     RamData_t tmp_out_data;
	 if (read_counter.y == 0)
	    valid <= 1'b1;
     else
	    valid <= 1'b0;
     if (read_counter.y == 63)
	   rd_mem_flag <= False;
     read_counter.y <= read_counter.y + 1;
     tmp_out_data = ram1.sub2(read_counter.y);     
     data_read_reg <= tmp_out_data;
	 //$display("reading ram1 addr = %d data = %h",read_counter.y,tmp_out_data);
     //data_read_reg <= ram1.sub2(read_counter.y);     
   endrule

   //rule alwaysreadRAMB ((write_counter.x == StateA) && rd_mem_flag);
   rule alwaysreadRAMB ((read_counter.x == StateB) && rd_mem_flag);
     RamData_t tmp_out_data;
	 if (read_counter.y == 0)
	    valid <= 1'b1;
     else
	    valid <= 1'b0;
     if (read_counter.y == 63)
	   rd_mem_flag <= False;
     read_counter.y <= read_counter.y + 1;
     tmp_out_data = ram2.sub2(read_counter.y);     
     data_read_reg <= tmp_out_data;
	 //$display("reading ram2 addr = %d data = %h",read_counter.y,tmp_out_data);
     //data_read_reg <= ram2.sub2(read_counter.y);     
   endrule

   method Action write_d (a);
     wr_data.wset (a) ;
   endmethod : write_d 

   method Action read_d (Tuple2#(Bit#(1),RamAddr_t) a);
     rd_data.wset (a) ;
   endmethod : read_d 

   method Action clear_d (s);
     clear_reg.wset(?);
   endmethod : clear_d

   method Action sent_output_data (s);
     sent_reg.wset(s);
   endmethod : sent_output_data

  method RamData_t wr_data_read;
    wr_data_read = out_data; 
  endmethod : wr_data_read

  method RamData_t data_out;
    data_out = data_read_reg; 
  endmethod : data_out

  method Bit#(1)   data_valid;
    data_valid = valid; 
  endmethod : data_valid

  method Bool busy;
    busy = rd_mem_flag; 
  endmethod : busy

endmodule: mkCBuffer

endpackage: CBuffer
