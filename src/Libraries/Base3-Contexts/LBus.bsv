package LBus;

import ModuleContext::*;
import Counter::*;
import Vector::*;
import List::*;
import ConfigReg::*;
import GetPut::*;
import ClientServer::*;
import Connectable::*;
import RAM::*;
import HList::*;

// The LBus package provides a way to create registers that are accessible
// through some type of local bus (e.g., PCI).

// DEFAULT VALUES:

typedef 24 LBUS_ADDR_SIZE;
typedef 32 LBUS_DATA_SIZE;

typedef    LBusContextP#(LBUS_ADDR_SIZE, LBUS_DATA_SIZE) LBusContext;
typedef LBusContextIfcP#(LBUS_ADDR_SIZE, LBUS_DATA_SIZE) LBusContextIfc;

LBusContext initLBusContext = LBusContextP{ items: Nil, leaves: Nil };

// ABBREVIATIONS:

typedef LBUS_ADDR_SIZE SA;
typedef LBUS_DATA_SIZE SD;

// TYPES AND INTERFACES:

// The LBSReg type is normally never seen by a user of the LbSModule; it is
// only needed when creating new kinds of local bus registers.  This LBSReg
// interface is what the local bus uses to access a register.

interface LBSReg #(type sa, type sd);
    method LbAddr#(sa,sd)         lbsAddr();
    method Action                 lbsSet( Bit#(sd) x1);
    method ActionValue#(Bit#(sd)) lbsGet();
endinterface: LBSReg

// Note that the lbsGet method allows an action to be performed when the local
// bus reads the value.  This allows implementing, e.g., clear-on-read
// registers.

interface IntFlag #(type sa, type sd);
    method Bit#(1) flag();
endinterface: IntFlag

typedef union tagged {
    LBSReg#(sa, sd) Rg;
    IntFlag#(sa, sd) Flg;
} LBSItem #(type sa, type sd);

// The type LbAddr is the address used to get and set registers from the local
// bus.  (This type is exported abstractly.)

typedef union tagged {
    Bit#(sa) LbAddr;
} LbAddr #(type sa, type sd) deriving (Literal, Eq, Bits);

function Bit#(sa) unLbAddr(LbAddr#(sa,sd) x);
   case (x) matches
      tagged LbAddr .a: return (a);
      default: return(?); // cannot happen
   endcase
endfunction: unLbAddr

function LbAddr#(sa,sd) lbB2W(LbAddr#(sa,sd) x);
   case (x) matches
      tagged LbAddr .a: return (LbAddr (a >> 2));
      default: return (?); // cannot happen
   endcase
endfunction: lbB2W

// The local bus registers are collected automagically by the ModuleCollect
// monad.  An LbSModule#(sa,sd,i) corresponds to a Module#(i) except that it
// also keeps a set of registers.  The address is sa bits wide and data items
// are sd bits wide.

typedef struct {
   List#(LBSItem#(sa, sd)) items;
   List#(ILbLeaf#(sa, sd)) leaves;
                } LBusContextP#(numeric type sa, numeric type sd); // P for polymorphic

typedef ILbLeaf#(sa, sd) LBusContextIfcP#(numeric type sa, numeric type sd); // P for polymorphic

interface IWithLBus#(type busIfc, type deviceIfc);
  interface busIfc    bus;
  interface deviceIfc device;
endinterface

typedef IWithLBus#(LBSReg#(sa, sd), i) LBReg#(type sa, type sd, type i);

module [mc] lbs#(Module#(LBReg#(sa, sd, i)) m)(i)
   provisos (IsModule#(mc, _a), Context#(mc, LBusContextP#(sa,sd)));

   (*hide*)LBReg#(sa, sd, i) bd <- liftModule(m);

   LBusContextP#(sa,sd) c <- getContext();
   c.items = Cons(tagged Rg bd.bus, c.items);
   putContext(c);

   return(bd.device);
endmodule

module [mc] lbsInt#(mc#(IWithLBus#(IntFlag#(sa, sd), i)) m)(i)
   provisos (IsModule#(mc, _a), Context#(mc, LBusContextP#(sa,sd)));

   IWithLBus#(IntFlag#(sa,sd), i) bd <- m;

   LBusContextP#(sa,sd) c <- getContext();
   c.items = Cons(tagged Flg bd.bus, c.items);
   putContext(c);

   return(bd.device);
endmodule: lbsInt

// CREATING REGISTERS

typedef enum { SYNC, ASYNC, NONE } ResetType deriving (Bits, Eq);

module regRW#(ResetType syncType, LbAddr#(sa,sd) aw, Integer an, r x)(LBReg#(sa, sd, Reg#(r)))
   provisos (Bits#(r, sr), Add#(k, sr, sd));

   Reg#(r) r <- (syncType== SYNC ? mkReg(x) :
		 syncType==ASYNC ?mkRegA(x) :
		 mkRegU);
   (*hide*) Reg#(r) w <- mkWire;

   let vsr =  valueOf(sr);
   let vsd =  valueOf(sd);
   if (vsr + an > vsd) begin
      let sr_s = integerToString(vsr);
      let an_s = integerToString(an);
      let aw_s = bitToString(unLbAddr(aw));
      String s = "LBus register: field won't fit.                 " +
      "LBus address (decimal) " + aw_s +
      ", offset " + an_s +", field length " + sr_s;
      error(s);
   end
   (*hide, fire_when_enabled*)
   rule complete_write;
      r <= w;
   endrule

   interface LBSReg bus;
      method lbsAddr();
         return (aw);
      endmethod: lbsAddr

      method Action lbsSet(v);
         w <= unpack(truncate(v >> fromInteger(an)));
      endmethod: lbsSet

      method ActionValue#(Bit#(sd)) lbsGet();
         actionvalue
            Bit#(sd) tmp = zeroExtend(pack(r));
            return(tmp << fromInteger(an));
         endactionvalue
      endmethod: lbsGet
   endinterface: bus

   interface device = asReg(r);
endmodule: regRW

// The mkLbRegRW module creates a register that looks like
// a normal register in the module that creates it, but it is also
// accessible from the local bus at the given address.

module [mc] mkLbRegRW#( LbAddr#(SA,SD) aw, Integer an, r_type x)
              ( Reg#(r_type))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r_type, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRW(SYNC, aw, an, x));
   return(ifc);
endmodule: mkLbRegRW


module [mc] mkLbWdRW#(LbAddr#(SA,SD) aw, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRW(SYNC, aw, 0, x));
   return(ifc);
endmodule: mkLbWdRW

module [mc] mkLbRegRWA#( LbAddr#(SA,SD) aw, Integer an, r_type x)
              ( Reg#(r_type))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r_type, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRW(ASYNC, aw, an, x));
   return(ifc);
endmodule: mkLbRegRWA


module [mc] mkLbWdRWA#(LbAddr#(SA,SD) aw, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRW(ASYNC, aw, 0, x));
   return(ifc);
endmodule: mkLbWdRWA

module [mc] mkLbRegRWU#( LbAddr#(SA,SD) aw, Integer an)
              ( Reg#(r_type))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r_type, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRW(NONE, aw, an, ?));
   return(ifc);
endmodule: mkLbRegRWU


module [mc] mkLbWdRWU#(LbAddr#(SA,SD) aw)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
	     Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRW(NONE, aw, 0, ?));
   return(ifc);
endmodule: mkLbWdRWU

module regW1tC#(LbAddr#(sa,sd) aw, Integer an, Bit#(1) x)(LBReg#(sa, sd, Reg#(Bit#(1))))
   provisos (Add#(k, 1, sd));

   Reg#(Bit#(1)) r <- mkReg(x);

   let vsd =  valueOf(sd);
   if(1 + an > vsd)
      error("regW1tC: field won't fit");

   interface LBSReg bus;
      method lbsAddr();
         return (aw);
      endmethod: lbsAddr

      method Action lbsSet(v);
         r <= unpack(pack(r) & invert(truncate(v >> fromInteger(an))));
      endmethod: lbsSet

      method lbsGet();
         actionvalue
            Bit#(sd) tmp = zeroExtend(pack(r));
            return(tmp << fromInteger(an));
         endactionvalue
      endmethod: lbsGet
   endinterface: bus

   interface device = asReg(r);

endmodule: regW1tC

module [mc] mkLbRegW1tC#(LbAddr#(SA,SD) aw, Integer an, Bit#(1) x)(Reg#(Bit#(1)))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, 1, SD));
   (*hide*) let ifc <- lbs(regW1tC(aw, an, x));
   return(ifc);
endmodule: mkLbRegW1tC

module regRO#(ResetType syncType, LbAddr#(sa,sd) aw, Integer an, r x)(LBReg#(sa, sd, Reg#(r)))
   provisos (Bits#(r, sr), Add#(k, sr, sd));

   Reg#(r) r <- (syncType== SYNC ? mkReg(x) :
		 syncType==ASYNC ?mkRegA(x) :
		 mkRegU);

   let vsr =  valueOf(sr);
   let vsd =  valueOf(sd);
   if (vsr + an > vsd)
      error("regRO: field won't fit");

   interface LBSReg bus;
      method lbsAddr();
         return (aw);
      endmethod: lbsAddr

      method Action lbsSet(v);
      endmethod: lbsSet

      method lbsGet();
         actionvalue
            Bit#(sd) tmp = zeroExtend(pack(r));
            return(tmp << fromInteger(an));
         endactionvalue
      endmethod: lbsGet
   endinterface: bus

   interface device = asReg(r);
endmodule: regRO

// The mkLbRegRO module creates a register that looks like
// a normal register in the module that creates it, but it is also
// accessible from the local bus at the given address.
// From the local bus the register is read-only; attempts to write it
// have no effect.
// The created register has to have a bit width smaller than or equal to the
// local bus width.  If it is smaller it will padded with zeroes on the left.

module [mc] mkLbRegRO#(LbAddr#(SA,SD) aw, Integer an, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRO(SYNC, aw, an, x));
   return(ifc);
endmodule: mkLbRegRO

module [mc] mkLbWdRO#(LbAddr#(SA,SD) aw, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRO(SYNC, aw, 0, x));
   return(ifc);
endmodule: mkLbWdRO

module [mc] mkLbRegROA#(LbAddr#(SA,SD) aw, Integer an, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRO(ASYNC, aw, an, x));
   return(ifc);
endmodule: mkLbRegROA

module [mc] mkLbWdROA#(LbAddr#(SA,SD) aw, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRO(ASYNC, aw, 0, x));
   return(ifc);
endmodule: mkLbWdROA

module [mc] mkLbRegROU#(LbAddr#(SA,SD) aw, Integer an)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRO(NONE, aw, an, ?));
   return(ifc);
endmodule: mkLbRegROU

module [mc] mkLbWdROU#(LbAddr#(SA,SD) aw)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, SD));
   (*hide*) let ifc <- lbs(regRO(NONE, aw, 0, ?));
   return(ifc);
endmodule: mkLbWdROU

module [mc] mkLbConfigRegRO#(LbAddr#(SA,SD) aw, Integer an, r x)(Reg#(r))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Bits#(r, sr), Add#(k, sr, SD));
   (*hide*) let ifc <- lbs(regRO(SYNC, aw, an, x));
   Wire#(r) w <- mkWire;
   (* fire_when_enabled *) rule commit; ifc <= w; endrule
   method _write = w._write;
   method _read  = ifc._read;
endmodule: mkLbConfigRegRO

interface Accum #(type n);
    method Action add(Bit#(n) x1);
    method Bit#(n) value();
endinterface: Accum

module accum#(LbAddr#(sa,sd) aw, Integer an, Bit#(k) x)(LBReg#(sa, sd, Accum#(k)))
   provisos (Add#(k, i, sd));

   Counter#(k) c <- mkCounter(x);
   PulseWire getting <- mkPulseWire;

   let vk =  valueOf(k);
   let vsd =  valueOf(sd);
   if (vk + an > vsd)
      error("accum: field won't fit");

   interface LBSReg bus;
      method lbsAddr();
         return (aw);
      endmethod: lbsAddr

      method Action lbsSet(v);
         c.setF(truncate(v >> fromInteger(an)));
      endmethod: lbsSet

      method lbsGet();
         actionvalue
            getting.send();
            c.setC(0);
            Bit#(sd) tmp = zeroExtend(c.value);
            return(tmp << fromInteger(an));
         endactionvalue
      endmethod: lbsGet
   endinterface: bus

   interface Accum device;
      method add if (!getting) = c.inc;
      method value = c.value;
   endinterface: device
endmodule: accum

module [mc] mkLbAccum#(LbAddr#(SA,SD) aw, Integer an, Bit#(k) x)(Accum#(k))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, i, SD));
   (*hide*) let ifc <- lbs(accum(aw, an, x));
   return(ifc);
endmodule: mkLbAccum

interface Interrupt;
   method Action set();
   method Bool   _read();
endinterface: Interrupt

module w1tc#(LbAddr#(sa,sd) aw, Integer an)(LBReg#(sa, sd, Reg#(Bit#(1))))
   provisos (Add#(k, 1, sd));

   Reg#(Bit#(1)) r <- mkReg(0);
   Reg#(Bit#(1)) s <- mkReg(0);
   PulseWire setting <- mkPulseWire;

   rule transfer (!setting);
      r <= r | s;
      s <= 0;
   endrule: transfer

   interface LBSReg bus;
      method lbsAddr();
         return (aw);
      endmethod: lbsAddr

      method Action lbsSet(v);
         if ((v >> fromInteger(an))[0]==1)
            begin
               r <= s;
               setting.send();
            end
      endmethod: lbsSet

      method lbsGet();
         actionvalue
            Bit#(sd) tmp = zeroExtend(r);
            return(tmp << fromInteger(an));
         endactionvalue
      endmethod: lbsGet
   endinterface: bus

   interface Reg device;
      method _read();
         return (r);
      endmethod: _read

      method Action _write(x);
         s <= 1;
      endmethod: _write
   endinterface: device
endmodule: w1tc

module [mc] mkLbW1tC#(LbAddr#(SA,SD) aw, Integer an)(Reg#(Bit#(1)))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, 1, SD));
   (*hide*) let ifc <- lbs(w1tc(aw, an));
   return(ifc);
endmodule: mkLbW1tC

module [mc] interrupt#(LbAddr#(SA,SD) aw1, Integer an1, LbAddr#(SA,SD) aw2, Integer an2)
   (IWithLBus#(IntFlag#(SA,SD), Interrupt))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, 1, SD));

   Reg#(Bit#(1)) r <- mkLbW1tC(aw1, an1);
   Reg#(Bit#(1)) m <- mkLbRegRW(aw2, an2, 0);

   interface IntFlag bus;
      method flag();
         return (r & invert(m));
      endmethod: flag
   endinterface: bus

   interface Interrupt device;
      method Action set();
            r <= 1;
      endmethod: set
      method _read = (r == 1);
   endinterface: device
endmodule: interrupt

module [mc]
   mkLbInterrupt#(LbAddr#(SA,SD) aw1, Integer an1, LbAddr#(SA,SD) aw2, Integer an2)
       (Interrupt)
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, 1, SD));

   (*hide*) let ifc <- lbsInt(interrupt(aw1, an1, aw2, an2));
   return(ifc);
endmodule: mkLbInterrupt

interface RegHandler #(type a, type b);
    method a getRequest();
    method Action storeResponse(b x1);
endinterface: RegHandler

module [mc] mkLbClient#(LbAddr#(SA,SD) reqw, Integer reqn,
                        LbAddr#(SA,SD) ackw, Integer ackn,
                        mc#(RegHandler#(a, b)) mkRH)
        (Client#(a,b))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext),
             Add#(k, 1, SD));

   RegHandler#(a, b) rh <- mkRH;
   Reg#(Bit#(1)) req <- mkLbRegRW(reqw, reqn, 0);
   Reg#(Bit#(1)) ack <- mkLbRegW1tC(ackw, ackn, 0);
   Reg#(Bit#(1)) prevReq <- mkReg(0);
   Reg#(Bool)    reqFlag <- mkReg(False);

   rule trigger;
      prevReq <= req;
      if (prevReq == 0 && req == 1)
         reqFlag <= True;
   endrule: trigger

   interface Get request;
      method get() if (reqFlag) ;
         actionvalue
            reqFlag <= False;
            return(rh.getRequest);
         endactionvalue
      endmethod: get
   endinterface: request

   interface Put response;
      method Action put(x) ;
            rh.storeResponse(x);
            ack <= 1;
      endmethod: put
   endinterface: response
endmodule: mkLbClient


// The mkLbOffset function can be used to add an offset to all local
// bus register addresses in an LbSModule.

module [mc] mkLbOffset#(LbAddr#(SA,SD) a, mc#(i) m)(i)
   provisos (IsModule#(mc, _a), Context#(mc, LBusContext));

   function LBSItem#(SA,SD) f(LBSItem#(SA,SD) x);
      case (a) matches
         tagged LbAddr .o:
            case (x) matches
               tagged Rg .r:
                  return (tagged Rg (interface LBSReg;
                                        method lbsAddr();
                                           return (LbAddr (unLbAddr(r.lbsAddr) + o));
                                        endmethod: lbsAddr
                                        method lbsSet = r.lbsSet;
                                        method lbsGet = r.lbsGet;
                                     endinterface: LBSReg));
               default: return (x);
            endcase
         default: return (?); // cannot happen
      endcase
   endfunction

   LBusContext c <- getContext();
   c.items = List::map(f, c.items);
   putContext(c);

   (*hide*) let ifc <- m;
   return (ifc);
endmodule


// COLLECTING REGISTERS TOGETHER

// The external interface of a local bus is as follows.
// It is through this interface that register accesses normally happen.

typedef enum {LbRead, LbWrite} LbRWop deriving (Bits, Eq);

(*always_ready, always_enabled*)
interface ILBus #(type sa, type sd);
    method Action req(Bool valid, LbRWop op, Bit#(sa) addr, Bit#(sd) dat);
    method Bit#(sd) rdDat();
    method Bit#(1) ack();
    method Bit#(1) inrpt();
endinterface: ILBus

typedef struct {
    LbRWop   wr;
    Bit#(sa) adr;
    Bit#(sd) dat;
                } LbReq#(type sa, type sd) deriving (Bits, Eq);

interface ILbLeaf#(type sa, type sd);
   interface Put#(Maybe#(LbReq#(sa, sd))) req;
   interface Get#(Maybe#(Bit#(sd))) ack;
   (*always_ready*)
   interface Get#(Bit#(1)) inrpt;
endinterface: ILbLeaf

interface ILbNode#(type sa, type sd);
   interface Get#(Maybe#(LbReq#(sa, sd))) req;
   interface Put#(Maybe#(Bit#(sd))) ack;
   interface Put#(Bit#(1)) inrpt;
endinterface: ILbNode

instance Connectable#(ILbLeaf#(sa, sd), ILbNode#(sa, sd));
   module mkConnection#(ILbLeaf#(sa, sd) l, ILbNode#(sa, sd) n)(Empty);
      mkConnection(l.req, n.req);
      mkConnection(l.ack, n.ack);
      mkConnection(l.inrpt, n.inrpt);
   endmodule
endinstance

// Given a LbSModule with a set of register we can extract
// the local bus interface and the normal interface.

instance Expose#(LBusContextP#(sa,sd), LBusContextIfcP#(sa,sd), CLOCKCONTEXTSIZE);
   module unburyContext#(LBusContextP#(sa,sd) lbc)(LBusContextIfcP#(sa,sd));
      function isReg(x);
         case (x) matches
            tagged Rg .* : return True;
            default :      return False;
         endcase
      endfunction: isReg
      function isFlag(x);
         case (x) matches
            tagged Flg .* : return True;
            default :       return False;
         endcase
      endfunction: isFlag
      function theReg(x);
         case (x) matches
            tagged Rg .y :  return (y);
            default:        return (?); // cannot happen
         endcase
      endfunction: theReg
      function theFlag(x);
         case (x) matches
            tagged Flg .y : return (y.flag);
            default:        return (?); // cannot happen
         endcase
      endfunction: theFlag

      let lbs = lbc.items;
      let leaves = lbc.leaves;

      if (length(lbs)!=0)
         begin
            let regs =  List::map(theReg, List::filter(isReg, lbs));
            let flags =  List::map(theFlag, List::filter(isFlag, lbs));
            let interruption =  foldt(or_f, 0, flags);

            Reg#(LbReq#(sa, sd)) reqtX <- mkConfigReg(?);
            Reg#(LbReq#(sa, sd)) reqt  <- mkConfigReg(?);
            Reg#(Bit#(sd))       ackt  <- mkConfigReg(?);
            Reg#(Bool)        reqFlag  <- mkConfigReg(False);
            Reg#(Bool)        ackFlag  <- mkConfigReg(False);
            Reg#(Bool)       reqFlagX  <- mkConfigReg(False);
            Reg#(Bit#(1))       iFlag  <- mkConfigReg(0);

            (* fire_when_enabled, no_implicit_conditions *)
            rule clear_ackFlag (ackFlag);
               ackFlag <= False;
            endrule: clear_ackFlag

            (* fire_when_enabled, no_implicit_conditions *)
            rule set_iFlag;
               iFlag <= interruption;
            endrule: set_iFlag

            (* fire_when_enabled, no_implicit_conditions *)
            rule transfer_reqFlag (reqFlagX);
               reqFlag <= True;
               reqt <= reqtX;
            endrule: transfer_reqFlag

            rule readAndWrite (reqFlag);
               reqFlag <= False;

               function g(lbi);
               return (actionvalue
                          if (unLbAddr(lbi.lbsAddr) == reqt.adr)
                             actionvalue
                                let v <- lbi.lbsGet;
                                return (v);
                             endactionvalue
                          else
                             actionvalue
                                return (0);
                             endactionvalue
                       endactionvalue);
               endfunction

               function h(lbi);
                  action
                     if (unLbAddr(lbi.lbsAddr) == reqt.adr)
                        lbi.lbsSet(reqt.dat);
                  endaction
               endfunction

               if (reqt.wr == LbRead)
                  action
                     ackFlag <= True;
                     let vs <- List::mapM(g, regs);
                     ackt <= foldt(or_f, 0, vs);
                  endaction
               else
                  List::joinActions(List::map(h, regs));
            endrule: readAndWrite

            ILbLeaf#(sa, sd) newLeaf = (
               interface ILbLeaf;
                  interface Put req;
                     method Action put(mr);
                        reqFlagX <= isJust(mr);
                        reqtX <= validValue(mr);
                     endmethod: put
                  endinterface: req
                  interface Get ack;
                     method get();
                        actionvalue
                           if (ackFlag)
                              return (tagged Valid ackt);
                           else
                              return (tagged Invalid);
                        endactionvalue
                     endmethod: get
                  endinterface: ack
                  interface Get inrpt;
                     method get() ;
                        actionvalue
                           return(iFlag);
                        endactionvalue
                     endmethod: get
                  endinterface: inrpt
               endinterface
                                        );
            leaves = Cons(newLeaf, leaves);
         end

      // Now deal with the leaves:
      let n = length(leaves);
      ILbLeaf#(sa, sd) resLeaf = ?;

      case (n)
	 1: resLeaf = List::head(leaves);
	 0: resLeaf = (
	    interface ILbLeaf;
	       interface Put req;
		  method Action put(mr);
		  endmethod: put
	       endinterface: req
	       interface Get ack;
		  method get();
		     actionvalue
			return (tagged Valid 0);
		     endactionvalue
		  endmethod: get
	       endinterface: ack
	       interface Get inrpt;
		  method get() ;
		     actionvalue
			return(0);
		     endactionvalue
		  endmethod: get
	       endinterface: inrpt
	    endinterface
		       );
	 default:
	 begin
	    Reg#(Maybe#(LbReq#(sa, sd))) maybeReq <- mkConfigReg(Invalid);

	    rule transmitReq;
	       for(Integer i = 0; i<n; i=i+1)
		  leaves[i].req.put(maybeReq);
	    endrule: transmitReq

	    List#(Reg#(Maybe#(Bit#(sd)))) acks <- List::replicateM(n, mkConfigReg(Invalid));
	    List#(Maybe#(Bit#(sd))) ackvs = List::map(readReg, acks);
	    for (Integer i = 0; i<n; i=i+1)
	       begin
		  rule receiveAck;
		     let x <- leaves[i].ack.get();
		     if (!isValid(acks[i])) (acks[i]) <= x;
		  endrule
	       end

	    Reg#(Maybe#(Bit#(sd))) ackr <- mkConfigReg(Invalid);

	    function f(x);
	    case (x) matches
	       tagged Invalid: return(0);
	       tagged Valid .y: return(y);
	    endcase
	    endfunction

	    rule registerAck (foldt(and_f, True, (List::map(isValid, ackvs))));
	       ackr <= Valid(foldt(or_f, 0, (List::map(f, ackvs))));
	       for (Integer i = 0; i<n; i=i+1)
		  action
		     (acks[i]) <= Invalid;
		  endaction
	    endrule

	    resLeaf = (
	       interface ILbLeaf;
		  interface Put req;
		     method Action put(mr);
			maybeReq <= mr;
		     endmethod: put
		  endinterface: req

		  interface Get ack;
		     method get();
		       actionvalue
			  if (isValid(ackr))
			     ackr <= Invalid;
			  return (ackr);
		       endactionvalue
		     endmethod: get
		  endinterface: ack

		  interface Get inrpt;
		     method get() ;
		       actionvalue
			  List#(Bit#(1)) intvs = List::replicate(n, ?);
			  for (Integer i = 0; i<n; i=i+1)
			     begin
				let x <- leaves[i].inrpt.get();
				intvs[i] = x;
			     end
			  return(foldt(or_f, 0, intvs));
		       endactionvalue
		     endmethod: get
		  endinterface: inrpt
	       endinterface
		       );
	 end
      endcase
      return resLeaf;
   endmodule
endinstance

// Once the registers have been collected into an ILbLeaf
// interface these interfaces can be collected together.

instance Hide#(mc, LBusContextIfcP#(sa,sd))
   provisos (IsModule#(mc, _a), Context#(mc, LBusContextP#(sa,sd)));

   module [mc] reburyContext#(LBusContextIfcP#(sa,sd) i)(Empty);
      LBusContextP#(sa,sd) c <- getContext();
      c.leaves = Cons(i, c.leaves);
      putContext(c);
   endmodule
endinstance

interface DutWithLBusIfc#(type i);
   interface i              dutIfc;
   interface LBusContextIfc lbus;
endinterface

typeclass LBusAddable#(type m1, type m2)
   dependencies (m1 determines m2, m2 determines m1);
   module [m1] runWithLBus#(m2#(ifcType) mkI)
      (DutWithLBusIfc#(ifcType));
endtypeclass

instance LBusAddable#(ModuleContext#(c1), ModuleContext#(HCons#(LBusContext,c1)));
   module [ModuleContext#(c1)] runWithLBus#(ModuleContext#(HCons#(LBusContext,c1), i) mkM)
      (DutWithLBusIfc#(i));

      match {.lbusc, .ifc} <- runWithContext(initLBusContext, mkM);
      let lifc <- unburyContext(lbusc);

      interface dutIfc = ifc;
      interface lbus   = lifc;
   endmodule
endinstance

instance LBusAddable#(Module, ModuleContext#(LBusContext));
   module [Module] runWithLBus#(ModuleContext#(LBusContext, i) mkM)
      (DutWithLBusIfc#(i));

      match {.lbusc, .ifc} <- runWithContext(initLBusContext, mkM);
      let lifc <- unburyContext(lbusc);

      interface dutIfc = ifc;
      interface lbus   = lifc;
   endmodule
endinstance

// =========================

// STUFF FOR AN ASIC TOP-LEVEL, TO ASSIST PRODUCTION OF FULLY REGISTERED
// HARDMACS CONNECTED ONLY BY WIRES

typedef enum {
  Idle, Req1, Req2, Req3} LbState deriving (Eq, Bits);

interface Fan#(type intype, type outtype);
   interface intype fanin;
   interface outtype fanout;
endinterface: Fan


// The mkLbTop module combines local bus register clusters.
// It introduces a one cycle latency on both request and response.

module [Module] mkLbTop#(Module#(Fan#(ILBus#(SA, SD), Vector#(1, ILbNode#(SA, SD)))) mkFanout,
                         ModuleContext#(LBusContext, i) lm) (IWithLBus#(ILBus#(SA, SD), i));

   match {.lbc, .ifc} <- runWithContext(initLBusContext, lm);
   let lbifc <- unburyContext(lbc);
   Fan#(ILBus#(SA, SD), Vector#(1, ILbNode#(SA, SD))) lbis <- mkFanout;

   mkConnection(lbifc, lbis.fanout[0]);

   interface device = ifc;
   interface bus = lbis.fanin;
endmodule: mkLbTop

module [Module] mkLbFanout(Fan#(ILBus#(SA, SD), Vector#(n, ILbNode#(SA, SD))));

   let nv = valueOf(n);
   let ns =  upto(1, valueOf(n));

   Reg#(LbState)                   state <- mkConfigReg(Idle);
   Reg#(Bit#(SD))                r_rdDat <- mkConfigReg(0);
   Reg#(Bit#(1))                 r_piAck <- mkConfigReg(0);
   Reg#(Bit#(1))                 r_piInt <- mkConfigReg(0);
   Reg#(Maybe#(LbReq#(SA, SD)))  request <- mkConfigReg(Invalid);
   Reg#(Maybe#(LbReq#(SA, SD))) requestX <- mkConfigReg(Invalid);

   List#(Reg#(Bit#(SD))) rdDats  <- List::replicateM(nv, mkConfigReg(?));
   List#(Reg#(Bit#(SD))) rdDatsX <- List::replicateM(nv, mkConfigReg(?));
   List#(Reg#(Bool))     acks    <- List::replicateM(nv, mkConfigReg(False));
   List#(Reg#(Bool))     acksX   <- List::replicateM(nv, mkConfigReg(False));
   List#(Reg#(Bit#(1)))  ints    <- List::replicateM(nv, mkConfigReg(0));

   function leafIfc(dat, akk, inpt);
      let ifc = (interface ILbNode;
                    interface Get req;
                       method get() ;
                          actionvalue
                             return(request);
                          endactionvalue
                       endmethod: get
                    endinterface: req
                    interface Put ack;
                       method Action put (x);
                          writeReg(akk,isValid(x));
                          writeReg(dat,validValue(x));
                       endmethod: put
                    endinterface: ack
                    interface Put inrpt;
                       method Action put(x) ;
                          writeReg(inpt,x);
                       endmethod: put
                    endinterface: inrpt
                 endinterface: ILbNode);
      return (ifc);
   endfunction: leafIfc

   function Rules ackFn(Reg#(Bool) a, Reg#(Bool) aX, Reg#(Bit#(sd)) d, Reg#(Bit#(sd)) dX);
      return (rules
                 rule ack (aX);
                    a <= True;
                    d <= dX;
                 endrule: ack
              endrules);
   endfunction: ackFn

   function idleFn(a) = writeReg(a,False);

   let ifcs =  Vector::toVector(List::zipWith3(leafIfc, rdDatsX, acksX, ints));

   let pi = (interface ILBus;
                method Action req(valid, o, a, d);
                   let s =  LbReq { wr : o, adr : a, dat : d};
                   if (valid)
                      requestX <= tagged Valid(s);
                   else
                      requestX <= tagged Invalid;
                endmethod: req
                method rdDat() ;
                   return (r_rdDat);
                endmethod: rdDat
                method ack();
                   return (r_piAck);
                endmethod: ack
                method inrpt();
                   return (r_piInt);
                endmethod: inrpt
             endinterface);

   function a f(Reg#(a) r);
      return (r);
   endfunction

   addRules(List::joinRules(List::zipWith4(ackFn, acks, acksX, rdDats, rdDatsX)));

   (* fire_when_enabled, no_implicit_conditions *)
   rule interrupt (True);
      r_piInt <= foldt(or_f, 0, List::map(f, ints));
   endrule: interrupt

   (* no_implicit_conditions *)
   rule piIdle (state == Idle);
      List::joinActions(List::map(idleFn, acks));
      r_piAck <= 0;
      if (isValid(requestX))
          action
             state <= Req1;
             request <= requestX;
          endaction
   endrule: piIdle

   (* no_implicit_conditions *)
   rule piReq1 (state == Req1);
         state <= Req2;
         request <= tagged Invalid;
   endrule: piReq1

   (* no_implicit_conditions *)
   rule piReq2 (state == Req2);
          if (foldt(and_f, True, List::map(f, acks)))
              action
                 state <= Req3;
                 r_rdDat <= foldt(or_f, 0, List::map(f, rdDats));
              endaction
   endrule: piReq2

   (* no_implicit_conditions *)
   rule piReq3 (state == Req3);
         state <= Idle;
         r_piAck <= 1;
   endrule: piReq3

   interface fanin = pi;
   interface fanout = ifcs;

endmodule: mkLbFanout

// TESTBENCH FACILITIES

interface ILBusDriver#(type sa, type sd);
   method Bool valid;
   method LbRWop op;
   method Bit#(sa) addr;
   method Bit#(sd) dat;
   method Action rdDat(Bit#(sd) x);
   method Action ack(Bit#(1) x);
   method Action inrpt(Bit#(1) x);
endinterface: ILBusDriver

instance Connectable#(ILBus#(sa,sd), ILBusDriver#(sa,sd));
   module mkConnection#(ILBus#(sa,sd) b, ILBusDriver#(sa,sd) d)(Empty);
      (* no_implicit_conditions, fire_when_enabled *)
      rule connectLb;
         b.req(d.valid, d.op, d.addr, d.dat);
         d.rdDat(b.rdDat);
         d.ack(b.ack);
         d.inrpt(b.inrpt);
      endrule
   endmodule
endinstance

instance Connectable#(ILBusDriver#(sa,sd), ILBus#(sa,sd));
   module mkConnection#(ILBusDriver#(sa,sd) d, ILBus#(sa,sd) b)(Empty);
      mkConnection(b, d);
   endmodule
endinstance

interface ILBusHandler#(type sa, type sd);
   interface ILBusDriver#(sa,sd) driver;
   interface RAM#(Bit#(sa),Bit#(sd)) lbserver;
   method Bool interrupting;
   method Action resetInterrupt;
endinterface: ILBusHandler

typedef enum {
    Idle, Writing, Reading } HandlerState deriving (Eq, Bits);

module mkLbHandler(ILBusHandler#(sa,sd));
   Reg#(Bool)      validr <- mkConfigReg(False);
   Reg#(LbRWop)      opr  <- mkConfigReg(?);
   Reg#(Bit#(sa))   addrr <- mkConfigReg(?);
   Reg#(Bit#(sd))    datr <- mkConfigReg(?);
   Reg#(Bit#(sd))  rddatr <- mkConfigReg(?);
   Reg#(Bit#(sd)) rddatrX <- mkConfigReg(?);
   Reg#(Bool)        ackr <- mkConfigReg(False);
   Reg#(Bool)       ackrX <- mkConfigReg(False);
   Reg#(Bool)      inrptr <- mkConfigReg(False);
   Reg#(Bool)     inrptrX <- mkConfigReg(False);

   Reg#(HandlerState) state <- mkReg(Idle);

   rule setInterrupting (inrptr);
      inrptrX <= True;
   endrule

   rule setAck (state != Idle && ackr);
      if (state==Writing)
         state <= Idle;
      else
         action
            ackrX <= True;
            rddatrX <= rddatr;
         endaction
   endrule

   rule endReq (validr);
      validr <= False;
   endrule

   interface Server lbserver;
      interface Put request;
         method Action put(x) if (state == Idle && !validr);
            validr <= True;
            case (x) matches
               tagged Read .a:
                  begin
                     opr <= LbRead;
                     addrr <= a;
                     state <= Reading;
                  end
               tagged Write {.a, .d}:
                  begin
                     opr <= LbWrite;
                     addrr <= a;
                     datr <= d;
                     state <= Writing;
                  end
            endcase
         endmethod
      endinterface: request
      interface Get response;
         method get() if (state==Reading && ackrX);
            actionvalue
               ackrX <= False;
               state <= Idle;
               return (rddatr);
            endactionvalue
         endmethod
      endinterface
   endinterface: lbserver


   method interrupting;
      return (inrptrX);
   endmethod

   method Action resetInterrupt;
      inrptrX <= False;
   endmethod

   interface ILBusDriver driver;
      method valid = validr;
      method op = opr;
      method addr =  addrr;
      method dat =  datr;
      method Action rdDat(x); rddatr <= x; endmethod
      method Action ack(x); ackr <= unpack(x); endmethod
      method Action inrpt(x); inrptr <= unpack(x);  endmethod
   endinterface: driver

endmodule: mkLbHandler

// SOME UTILITIES:

// A variant of a BSV library definition: takes an extra parameter, to be used
// in the (previously disallowed) case where the list argument is Nil:

function a foldt(function a f(a x1, a x2), a x, List#(a) xs);
    case (xs) matches
       tagged Nil: return (x);
       default: return (List::fold(f, xs));
    endcase
endfunction: foldt

// The function form of two BSV infix operators, needed in folding operations
// above:

function Bit#(n) or_f( Bit#(n) x,  Bit#(n) y) = (x | y);
function Bool and_f(Bool x, Bool y)          = (x && y);


endpackage: LBus
