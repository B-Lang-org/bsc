import ClientServer :: * ;
import DefaultValue :: * ;
import FIFOF::*;
import GetPut :: *;

`define TLM_PRM_DCL numeric type id_size,   \
                    numeric type addr_size, \
                    numeric type data_size, \
                    numeric type uint_size, \
                    type cstm_type

`define TLM_PRM    id_size,   \
                   addr_size, \
                   data_size, \
                   uint_size, \
                   cstm_type

`define TLM_PRM_STD 4,  \
                    32, \
                    32, \
                    10, \
                    Bit#(0)

module mkTLMBRAM (BRAMServer#(Bit#(anx), Bit#(dn)) bramifc,
                  TLMRecvIFC#(reqt, respt) ifc)
   provisos(Bits#(respt, sr),
            DefaultValue#(TLMResponse#(`TLM_PRM)),
            // byte_size needs to be a power of 2 (i.e. 1, 2, 4 ..)
            Div#(data_size, 8, byte_size),
            Add#(anx, TLog#(byte_size), an),
            Add#(anx, iax, addr_size),
            Add#(an, ia, addr_size),
            Add#(dn, id, data_size),
            Add#(TDiv#(dn,8), xn, byte_size),
//            Div#(data_size,8,TDiv#(data_size,8)),
            TLMRequestTC#(reqt,   `TLM_PRM),
            TLMResponseTC#(respt, `TLM_PRM)
      );

   BRAMServerBE#(Bit#(anx), Bit#(dn), TDiv#(dn,8)) bram_be = toBRAMServerBE(bramifc);
   let _z <- mkTLMBRAMBE(bram_be);
   return _z;

endmodule

// A module which provides a TLMRecv interface, built on any module that
// provides a BRAM1Port interface for example a mkBRAM module.
module mkTLMBRAMBE (BRAMServerBE#(Bit#(anx), Bit#(dn), nn) bramifc, TLMRecvIFC#(reqt, respt) ifc)
   provisos(Bits#(respt, sr),
            DefaultValue#(TLMResponse#(`TLM_PRM)),
            // byte_size needs to be a power of 2 (i.e. 1, 2, 4 ..)
            Div#(data_size, 8, byte_size),
            Add#(anx, TLog#(byte_size), an),
            Add#(anx, iax, addr_size),
            Add#(an, ia, addr_size),
            Add#(dn, id, data_size),
            Add#(nn, xn, byte_size),
            Div#(data_size,8,TDiv#(data_size,8)),
            TLMRequestTC#(reqt,   `TLM_PRM),
            TLMResponseTC#(respt, `TLM_PRM)
      );

   BRAMServerBE#(TLMAddr#(`TLM_PRM), TLMData#(`TLM_PRM), byte_size) bram = convertBRAMType (bramifc);

   FIFOF#(TLMCommand)  fifo_op       <- mkFIFOF;

   interface Get tx;
      method ActionValue#(respt) get () ;
         let val <- bram.response.get;
         let cmd = fifo_op.first;
         fifo_op.deq;
         TLMResponse#(`TLM_PRM) response = defaultValue ;
         response.data = {0,val};
         response.command = cmd;
         response.status  = SUCCESS; // Assume always OK if we get a response from the BRAM
         return fromTLMResponse(response);
      endmethod
   endinterface
   interface Put rx;
      method Action put (reqt req);
         case (toTLMRequest(req))  matches
            tagged Descriptor .d : begin
               case (d.command)
                  READ: begin
                           TLMAddr#(`TLM_PRM) addr = {0, (d.addr >> valueOf(TLog#(byte_size)))};
                           bram.request.put( BRAMRequestBE {writeen    :0,
                                                            responseOnWrite : True,
                                                            address  :addr,
                                                            datain   :0} );
                           fifo_op.enq(READ);
                        end
                  WRITE: begin
                            TLMAddr#(`TLM_PRM) addr = {0, (d.addr >> valueOf(TLog#(byte_size)))};
                            bram.request.put( BRAMRequestBE {writeen    : d.byte_enable,
                                                             responseOnWrite : True,
                                                             address  :addr,
                                                             datain   :d.data} );
                            fifo_op.enq(WRITE);
                         end
               endcase
            end
            tagged Data .d : begin
               $display( "ERROR: data stream sent: not supported");
            end
         endcase
      endmethod
   endinterface

endmodule


function BRAMServerBE#(TLMAddr#(`TLM_PRM), TLMData#(`TLM_PRM), n)
         convertBRAMType (BRAMServerBE#(Bit#(an), Bit#(dn), nn) ifcin)
            provisos (Add#(an, ai, addr_size),
                      Add#(dn, di, data_size),
                      Add#(nn, ni, n));
   return
   (interface Server;
       interface Put request;
          method Action put (reqin);
             let req = BRAMRequestBE {writeen   : truncate(reqin.writeen),
                                      responseOnWrite: True, // TLM has write response
                                      address : truncate(reqin.address),
                                      datain  : truncate(reqin.datain)};
             ifcin.request.put (req);
          endmethod
       endinterface
       interface Get response;
          method ActionValue#(TLMData#(`TLM_PRM)) get;
             let value <-  ifcin.response.get;
             return(extend(value));
          endmethod
       endinterface
    endinterface
    );
endfunction


typeclass ToBRAMSeverBETC #(type a, type addr, type data, numeric type n)
   dependencies (a determines (addr, data, n));
   function BRAMServerBE#(addr, data, n) toBRAMServerBE (a ifc);
endtypeclass

instance ToBRAMSeverBETC #(BRAMServerBE#(addr, data, n), addr, data, n);
   function toBRAMServerBE = id ;
endinstance

instance ToBRAMSeverBETC #(BRAMServer#(addr, data), addr, data, n);
   function BRAMServerBE#(addr, data, n) toBRAMServerBE ( BRAMServer#(addr, data) ifcin );
      return
      (interface Server;
          interface Put request;
             method Action put ( BRAMRequestBE#(addr, data, n) reqin);
                if ( (reqin.writeen != '0) && (reqin.writeen != '1) )
                   $display ("Converting from a BRAM Server to BRAM Server BE with invalid Byte enable %b",
                             reqin.writeen );
                let req = BRAMRequest {write    : reqin.writeen != 0,
                                       responseOnWrite: reqin.responseOnWrite,
                                       address : reqin.address,
                                       datain  : reqin.datain } ;
                ifcin.request.put (req);
       endmethod
          endinterface
          interface Get response;
             method ActionValue#(data) get;
                let value <-  ifcin.response.get;
                return(value);
       endmethod
          endinterface
       endinterface);
   endfunction
endinstance

// ----------------------------------------------------------------------

interface TLMRecvIFC#(type req, type resp);
   interface Get#(resp) tx;
   interface Put#(req)  rx;
endinterface

typedef struct {TLMCommand              command;
                TLMMode                 mode;
                TLMAddr#(`TLM_PRM)      addr;
                TLMData#(`TLM_PRM)      data;
                TLMUInt#(`TLM_PRM)      burst_length;
                TLMByteEn#(`TLM_PRM)    byte_enable;
                TLMBurstMode            burst_mode;
                TLMBurstSize#(`TLM_PRM) burst_size;
                TLMUInt#(`TLM_PRM)      prty;
                Bool                    lock;
                TLMId#(`TLM_PRM)        thread_id;
                TLMId#(`TLM_PRM)        transaction_id;
                TLMId#(`TLM_PRM)        export_id;
                TLMCustom#(`TLM_PRM)    custom;
                } RequestDescriptor#(`TLM_PRM_DCL) deriving (Eq, Bits, Bounded);

typedef struct {TLMData#(`TLM_PRM)   data;
                TLMId#(`TLM_PRM)     transaction_id;
                TLMCustom#(`TLM_PRM) custom;
                } RequestData#(`TLM_PRM_DCL) deriving (Eq, Bits, Bounded);


typedef union tagged {RequestDescriptor#(`TLM_PRM) Descriptor;
                      RequestData#(`TLM_PRM)       Data;
                      } TLMRequest#(`TLM_PRM_DCL) deriving(Eq, Bits, Bounded);

typedef struct {TLMCommand           command;
                TLMData#(`TLM_PRM)   data;
                TLMStatus            status;
                TLMUInt#(`TLM_PRM)   prty;
                TLMId#(`TLM_PRM)     thread_id;
                TLMId#(`TLM_PRM)     transaction_id;
                TLMId#(`TLM_PRM)     export_id;
                TLMCustom#(`TLM_PRM) custom;
                } TLMResponse#(`TLM_PRM_DCL) deriving (Eq, Bits, Bounded);

typeclass TLMRequestTC#(type a, `TLM_PRM_DCL)
   dependencies (a determines (`TLM_PRM));
   function TLMRequest#(`TLM_PRM) toTLMRequest(a value);
   function a                     fromTLMRequest(TLMRequest#(`TLM_PRM) value);
endtypeclass

typeclass TLMResponseTC#(type a, `TLM_PRM_DCL)
   dependencies (a determines (`TLM_PRM));
   function TLMResponse#(`TLM_PRM) toTLMResponse(a value);
   function a                      fromTLMResponse(TLMResponse#(`TLM_PRM) value);
endtypeclass

instance TLMRequestTC#(TLMRequest#(`TLM_PRM), `TLM_PRM);
   function toTLMRequest   = id;
   function fromTLMRequest = id;
endinstance

instance TLMResponseTC#(TLMResponse#(`TLM_PRM), `TLM_PRM);
   function toTLMResponse   = id;
   function fromTLMResponse = id;
endinstance

typedef enum {READ, WRITE, UNKNOWN}          	    TLMCommand   deriving(Bounded, Bits, Eq);
typedef enum {REGULAR, DEBUG, CONTROL, UNKNOWN}     TLMMode      deriving(Bounded, Bits, Eq);
typedef enum {INCR, WRAP, CNST, UNKNOWN}     	    TLMBurstMode deriving(Bounded, Bits, Eq);
typedef enum {SUCCESS, ERROR, NO_RESPONSE, UNKNOWN} TLMStatus    deriving(Bounded, Bits, Eq);

typedef Bit#(id_size)                    TLMId#(`TLM_PRM_DCL);
typedef Bit#(addr_size)                  TLMAddr#(`TLM_PRM_DCL);
typedef Bit#(data_size)                  TLMData#(`TLM_PRM_DCL);
typedef UInt#(uint_size)                 TLMUInt#(`TLM_PRM_DCL);
typedef Bit#(TDiv#(data_size, 8))        TLMByteEn#(`TLM_PRM_DCL);
typedef Bit#(TLog#(TDiv#(data_size, 8))) TLMBurstSize#(`TLM_PRM_DCL);
typedef cstm_type                        TLMCustom#(`TLM_PRM_DCL);

instance DefaultValue #(TLMResponse#(`TLM_PRM))
   provisos(DefaultValue#(cstm_type));
   function defaultValue ();
      TLMResponse#(`TLM_PRM) response;
      response.command        = READ;
      response.data           = 0;
      response.status         = SUCCESS;
      response.prty           = 0;
      response.thread_id      = 0;
      response.transaction_id = 0;
      response.export_id      = 0;
      response.custom         = defaultValue;
      return response;
   endfunction
endinstance

// ----------------------------------------------------------------------

typedef Server#(BRAMRequest#(addr, data), data) BRAMServer#(type addr, type data);

typedef Server#(BRAMRequestBE#(addr, data, n), data) BRAMServerBE#(type addr, type data, numeric type n);

typedef struct {
                Bool write;
                Bool responseOnWrite;
                addr address;
                data datain;
                } BRAMRequest#(type addr, type data) deriving(Bits, Eq);

typedef struct {
                Bit#(n) writeen;
                Bool    responseOnWrite;
                addr    address;
                data    datain;
                } BRAMRequestBE#(type addr, type data, numeric type n) deriving (Bits, Eq);

// ----------------------------------------------------------------------

