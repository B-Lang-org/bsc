////////////////////////////////////////////////////////////////////////////////
//  Filename      : Memory.bsv
//  Description   :
////////////////////////////////////////////////////////////////////////////////
package Memory;

// Notes :

////////////////////////////////////////////////////////////////////////////////
/// Imports
////////////////////////////////////////////////////////////////////////////////
import ClientServer      ::*;
import TieOff            ::*;
import DummyDriver       ::*;
import Vector            ::*;
import GetPut            ::*;
import RegFile           ::*;
import Connectable       ::*;
import FIFO              ::*;

Bool trace = False;

////////////////////////////////////////////////////////////////////////////////
/// Types
////////////////////////////////////////////////////////////////////////////////
typedef struct {
   Bool    write;
   Bit#(TDiv#(d,8)) byteen;
   Bit#(a) address;
   Bit#(d) data;
} MemoryRequest#(numeric type a, numeric type d) deriving (Bits, Eq, FShow);

typedef struct {
   Bit#(d)          data;
} MemoryResponse#(numeric type d) deriving (Bits, Eq, FShow);

typedef Server#(MemoryRequest#(a,d), MemoryResponse#(d))   MemoryServer#(numeric type a, numeric type d);
typedef Client#(MemoryRequest#(a,d), MemoryResponse#(d))   MemoryClient#(numeric type a, numeric type d);

////////////////////////////////////////////////////////////////////////////////
/// Functions
////////////////////////////////////////////////////////////////////////////////
function Bit#(n) maskdata(Bit#(n) origdata, Bit#(n) newdata, Bit#(1) mask)
   provisos (Add#(1,_x,n));
   return (newdata & signExtend(mask)) | (origdata & ~ signExtend(mask));
endfunction

function Bit#(d) updateDataWithMask(Bit#(d) origdata, Bit#(d) newdata, Bit#(d8) mask)
   provisos(Mul#(d8, 8, d));
   return pack(zipWith3(maskdata, unpack(zeroExtend(origdata)), unpack(zeroExtend(newdata)), unpack(mask)));
endfunction

////////////////////////////////////////////////////////////////////////////////
/// Instances
////////////////////////////////////////////////////////////////////////////////
instance DefaultValue#(MemoryRequest#(a,d));
   defaultValue = MemoryRequest {
      write:    False,
      byteen:   '1,
      address:  0,
      data:     0
      };
endinstance

instance DefaultValue#(MemoryResponse#(d));
   defaultValue = MemoryResponse {
      data:     0
      };
endinstance

instance TieOff#(MemoryClient#(a, d));
   module mkTieOff#(MemoryClient#(a, d) ifc)(Empty);
      Wire#(MemoryRequest#(a,d)) req <- mkWire;

      rule tie_off;
	 let r <- ifc.request.get;
	 req <= r;
      endrule
   endmodule
endinstance

instance DummyDriver#(MemoryClient#(a, d));
   module mkStub(MemoryClient#(a, d));
      interface Put response;
	 method Action put(i) if (False);
	    noAction;
	 endmethod
      endinterface
      interface Get request;
	 method ActionValue#(MemoryRequest#(a, d)) get() if (False);
	    return ?;
	 endmethod
      endinterface
   endmodule
endinstance

instance Connectable#(MemoryClient#(a, d), RegFile#(Bit#(ars), Bit#(d)))
   provisos (Add#(ars, __x, a)
             ,Mul#(TDiv#(d,8),8, d)
             )  ;

   // Allow connection between a memory client and RegFile as a memory server
   // The Regfile must be the same width, but the address size can be smaller in the regfile to
   // avoid simulation overhead.
   module mkConnection#(MemoryClient#(a,d) client, RegFile#(Bit#(ars), Bit#(d)) regfile)(Empty);

      FIFO#(Bit#(d)) read_results <- mkLFIFO;

      rule connect_requests;
         let request <- client.request.get;
         Bit#(ars) addr = truncate(request.address);
         Bit#(d) olddata = regfile.sub (addr) ;
         if (request.write) begin

            Bit#(d) newData = updateDataWithMask(olddata, request.data, request.byteen);
            regfile.upd(addr , newData);

            if (trace) $display("[%t] MEMORY WRITE %x %x %x", $time, request.byteen, request.address, request.data);
        end
        else begin
           read_results.enq(olddata);
           if (trace) $display("[%t] MEMORY READ %x %x", $time, request.address, olddata);
        end
      endrule

      rule connect_responses;
        let response = read_results.first; read_results.deq;
        client.response.put( MemoryResponse { data : response });
      endrule
    endmodule

endinstance

instance Connectable#(RegFile#(Bit#(ars), Bit#(d)), MemoryClient#(a,d))
   provisos (Add#(ars, __x, a)
             ,Mul#(TDiv#(d,8),8, d)
      )  ;
   // Allow connection between a memory client and RegFile as a memory server
   // The Regfile must be the same width, but the address size can be smaller in the regfile to
   // avoid simulation overhead.
   module mkConnection#(RegFile#(Bit#(ars), Bit#(d)) regfile, MemoryClient#(a,d) client )(Empty);
      (*hide*)
      Empty _c <- mkConnection( client, regfile);
   endmodule
endinstance

endpackage: Memory
