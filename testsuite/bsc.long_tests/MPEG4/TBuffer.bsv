/////////////////////////////////////////////////////////////////////////
/* Transpose Buffer.
   Consists of Two RAMs. Write row-wise and read col-wise.
   When you write into one of the rams, you read from the other.
*/

package TBuffer;

import SyncSRAM::*;
import SRAM::*;
import SPSRAM::*;
import RAM::*;
import ClientServer::*;
import GetPut::*;
import ConfigReg ::*;

// data and strobe
typedef Tuple2#(Int#(a), bit) DataStrobe#(type a)  ;

typedef Bit#(6)  RamAddr_t;
typedef Int#(16) RamData_t;

interface TBuffer_IFC#(type a);
   method Action start (DataStrobe#(a) data_a);
   method DataStrobe#(a)  result;
endinterface : TBuffer_IFC

typedef enum {StateA, StateB} States
    deriving (Eq, Bits);
typedef struct 
    { States    x;
      RamAddr_t y;
    } Count64
    deriving (Eq, Bits);

(* always_ready,
   always_enabled,
   synthesize *)
module mkTBuffer (TBuffer_IFC#(16) );

   // instantiate both RAMS
   RAM#(RamAddr_t,RamData_t) ram1();
   mkWrapSRAM #(mkSPSRAM(64)) the_ram1 (ram1);
   RAM#(RamAddr_t,RamData_t) ram2();
   mkWrapSRAM #(mkSPSRAM(64)) the_ram2 (ram2);
  
   Reg#(Count64) write_counter() ;
   mkConfigReg#(Count64 {x : StateA, y: 0}) i_write_counter(write_counter);
   
   Reg#(Bit#(6)) read_counter() ;
   mkConfigReg#(63) i_read_counter(read_counter) ;
   
   Reg#(Bool) write_valid() ;
   mkConfigReg#(False) i_write_valid(write_valid) ;

   RWire#(DataStrobe#(16)) in_data();
   mkRWire i_in_data(in_data) ;
   
   Reg#(RamData_t) out_data() ;
   mkReg#(0) i_out_data(out_data) ;
  
   rule writeRAMA (write_counter.x == StateA);
      if (in_data.wget matches tagged Just {.d,.s} )
           begin
            Tuple2#(RamAddr_t,RamData_t) a = tuple2((s==0)?write_counter.y:0,d);
            RAMreq#(RamAddr_t,RamData_t) b = Write(a);
            ram1.request.put (b);
         end 
         ram2.request.put (Read (read_counter));
   endrule

   rule writeRAMB (write_counter.x == StateB);
      if ( in_data.wget matches tagged Just( {.d,.s} ) )
         begin
            Tuple2#(RamAddr_t,RamData_t) a = tuple2((s==0)?write_counter.y:0,d);
            RAMreq#(RamAddr_t,RamData_t) b = Write(a);
            ram2.request.put (b);
            end
         ram1.request.put (Read (read_counter));
   endrule

   rule setReadCounter (read_counter != 63);
        Bit#(3) msb = read_counter [5:3];
        Bit#(3) lsb = read_counter [2:0];
        read_counter <= (msb == 3'b111) ? {msb+1,lsb+1} : {msb+1,lsb};
   endrule

   rule alwaysRead (True);
       RamData_t out1_data <- ram1.response.get;
       out_data <= out1_data;
   endrule
   
   rule alwaysRead2 (True);
       RamData_t out2_data <- ram2.response.get;
       out_data <= out2_data;
   endrule
       
       
   method Action start (a);
     in_data.wset (a) ;
     if ( tpl_2(a) == 1)
     begin
       write_counter <= Count64 { x: write_counter.x, y:1};
       write_valid <= True;
     end
     else if (write_counter.y == 63)
     begin
       write_counter <= Count64 { x: (write_valid?
                                     (write_counter.x==StateA?
                                                       StateB:StateA)
                                     :write_counter.x), 
                                  y:63};
       read_counter <= write_valid ? 0 : 63;
       write_valid <= False;
     end
     else
     begin
       write_counter <= Count64 { x:write_counter.x, y:write_counter.y+1};
     end
   endmethod : start 

   method result ();
       bit out_strobe = (read_counter == 40) ? 1 : 0;
       return tuple2(out_data,out_strobe);
   endmethod : result

endmodule: mkTBuffer

endpackage: TBuffer
