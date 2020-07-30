/*----------------------------------------------------------------------------

FiveStageCPUBypassPreFIFO
 
The modules in this file implement bypassing, but include a bypass from
the execute stage prior to the enqueue of into the buffer.  This means
that a value computed in the execute stage is available immediately in
the decode stage, rather than having to wait a cycle.  This creates
a longer path, but this longer cycle time may be an acceptable trade-off
in exchange for greater throughput.

There are several ways to implement this:
 
1) Define the logic for the execute stage outside of the execute rule.
   Then use that logic both inside the execute rule and inside the decode
   rule.  Common subexpression elimination should result in no duplication
   of logic in the circuit.

2) Instantiate an RWire and have the execute stage store its value in the
   RWire as well as enqueue into the FIFO.  Then the decode stage can
   probe the value of the RWire and bypass from this value.

3) Instead of explicitly instantiating an RWire, define a new FindFIFO
   module which has this pre-enq bypassing built-in.  (Essentially,
   bring the RWire into the FIFO module.)  The find method of the FIFO
   can return a bypass value based on any value being enqueued at the
   same time.  This version would have the benefit of requiring no change
   in the CPU module, other than to instantiate a different FindFIFO
   module.

Below, we implement #3.
  
-----------------------------------------------------------------------------*/

import RegFile::*;
import FIFO::*;
import FIFOF::*;
import FindFIFOM2::*;

typedef enum
  { R0 , R1 , R2 , R3 , R4 , R5 , R6 , R7 ,
    R8 , R9 , R10, R11, R12, R13, R14, R15,
    R16, R17, R18, R19, R20, R21, R22, R23,
    R24, R25, R26, R27, R28, R29, R30, R31 } RName deriving (Bits, Eq);
  // typedef Bit#(5) RName;
  // Note: assume R0 reads 0, discards writes

typedef Bit#(32) Ia;   // Instruction address
typedef Bit#(32) Value;
typedef Bit#(10) Const;

typedef RName Src;
typedef RName Dest;
typedef RName Cond;
typedef RName Addr;
typedef RName Val;

typedef union tagged {
    struct { Dest rd; Src   ra; Src rb; } Add;
    struct { Cond cd; Addr  addr; }       Jz;
    struct { Dest rd; Addr  addr; }       Load;
    struct { Val  v;  Addr  addr; }       Store;
    struct { Dest rd; Const v; }          LoadC;
    void                                  Halt;
} Instr deriving (Bits);

typedef union tagged {
    struct { Dest  rd; Value ra; Value rb; } EAdd;
    struct { Value cd; Value addr; }         EJz;
    struct { Dest  rd; Value addr; }         ELoad;
    struct { Value v;  Value addr; }         EStore;
    struct { Dest  rd; Value v; }            ELoadC;
    void                                     EHalt;
} InstTemplate deriving (Bits);

// --------------------------------------------------------
// Register File

interface RegisterFile;
    method Value read1(RName x1);
    method Value read2(RName x1);
    method Action write(RName x1, Value x2);
endinterface: RegisterFile

module mkRegisterFile(RegisterFile);
  RegFile#(RName, Value) rs();
  mkRegFileWCF#(R0, R31) the_rs(rs);

  method read1(addr) ; return (addr == R0 ? 0 : rs.sub(addr)) ; endmethod
  method read2(addr) ; return (addr == R0 ? 0 : rs.sub(addr)) ; endmethod
  method write(addr, val) =  rs.upd(addr, val) ;
endmodule: mkRegisterFile

// --------------------------------------------------------
// Simple Memory Model

interface MemIF;
    method Bit#(32) get(Bit#(32) x1);
    method Action put(Bit#(32) x1, Bit#(32) x2);
endinterface: MemIF

module mkMem(MemIF);
  RegFile#(Bit#(8), Bit#(32)) arr();
  mkRegFileFull the_arr(arr);

  method get(a) ; return arr.sub(truncate(a)) ; endmethod
  method put(a, v) = arr.upd(truncate(a), v) ;
endmodule: mkMem

// -------------------------------------------------------
// The Unpipelined Processor

interface CPU;
    method MemIF imem();
    method MemIF dmem();
    method Action start();
    method Bool   done();
endinterface: CPU

module mkFiveStageCPUBypassPreFIFO(CPU);

  // ----------------------------
  // Internal state

  MemIF instrMem();
  mkMem the_instrMem(instrMem);

  MemIF dataMem();
  mkMem the_dataMem(dataMem);

  RegisterFile rf();
  mkRegisterFile the_rf(rf);

  Reg#(Ia) pc();
  mkReg#(0) the_pc(pc);

  // Buffer after the fetch stage
  // Contains: pc, instr
  FIFO#(Tuple2#(Ia, Bit#(32))) bf();
  mkLFIFO the_bf(bf);

  // Buffer after the decode stage
  // Contains: pc, instr template
  //   Since we are now examining the computation on the output of
  //   this buffer for stalling / bypassing, we must *not* stall
  //   based on the head of the buffer.  Since the buffer is only
  //   one element, we remove the find feature and use a normal FIFO.
  FIFOF#(Tuple2#(Ia, InstTemplate)) bd();
  mkLFIFOF the_bd(bd);

  // Buffer after the execute stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFOM#(Tuple2#(Ia, InstTemplate), Maybe#(Value)) be();
  mkFindFIFOBypassM the_be(be);

  // Buffer after the memory stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFOM#(Tuple2#(Ia, InstTemplate), Maybe#(Value)) bm();
  mkFindFIFOM the_bm(bm);

  // The CPU leaves reset in an idle state and does not start fetching
  // instructions until this register is set to True.
  Reg#(Bool) started();
  mkReg#(False) the_started(started);

  // ----------------------------
  // Convenience functions
   
  // Functions which check for stall and potential bypass.
  // Note: The functions don't check whether rd == R0.
  // R0's value never changes, so there is never a need to stall,
  // and one must *not* bypass.  This check is done in the
  // function "bypass" below.
   
  function findf_be(r, pci);
    case (tpl_2(pci)) matches

       tagged ELoad  {rd:.rd} :
	  if (r == rd)
	     return (Valid(Invalid)) ; // stall
          else
	     return (Invalid) ;

       tagged ELoadC {rd:.rd, v:.v} :
	  if (r == rd)
	     return (Valid(Valid(v))) ; // bypass
	  else
	     return (Invalid) ;

       default : return Invalid ;
    endcase
  endfunction: findf_be

  function findf_bm(r, pci);
    case (tpl_2(pci)) matches

       tagged ELoadC {rd:.rd, v:.v} :
	  if (r == rd)
	     return (Valid(Valid(v))) ; // bypass
	  else
	     return (Invalid);

       default : return (Invalid) ;
    endcase
  endfunction: findf_bm

  // Aliases for the lookup in each FIFO

  function beStall(r);
     case (be.find(findf_be(r))) matches
	tagged Valid (Invalid) : return True;
	default : return False;
     endcase
  endfunction

  function bmStall(r);
     case (bm.find(findf_bm(r))) matches
	tagged Valid (Invalid) : return True;
	default : return False;
     endcase
  endfunction

  // Bypass functions

  function beBypass(r);
     case (be.find(findf_be(r))) matches
	tagged Valid (tagged Valid .v) : return (Valid(v)) ;
	default : return (Invalid);
     endcase
  endfunction
  
  function bmBypass(r);
     case (bm.find(findf_bm(r))) matches
	tagged Valid (tagged Valid .v) : return (Valid(v)) ;
	default : return (Invalid);
     endcase
  endfunction
  
  // A single function which performs the stall check on all FIFOs
  function chk(r); return (beStall(r) || bmStall(r)); endfunction

  // Aliases for looking up a register's value in the register file

  function bypass(r,v);
     if (r == R0)
	return v; // don't bypass R0!
     else
     if (isValid(beBypass(r)))
	return validValue(beBypass(r));
     else
     if (isValid(bmBypass(r)))
	return validValue(bmBypass(r));
     else
	return v;
  endfunction

  function rval1(r); return bypass(r, rf.read1(r)); endfunction
  function rval2(r); return bypass(r, rf.read2(r)); endfunction


  // ----------------------------
  // The Fetch stage

  rule fetch (started);
     bf.enq(tuple2(pc, instrMem.get(pc)));
     pc <= pc + 1;
  endrule

  // ----------------------------
  // The Decode stage

  // Take a 32-bit value and convert it into the abstract representation
  function Instr toInstr(Bit#(32) i32);
    return (unpack(truncate(i32)));
  endfunction

  Rules decode_non_stall_rules = rules 
  rule decode_halt
         (bf.first matches {.dpc, .i32} &&&
          toInstr(i32) matches (tagged Halt));
     // Atomicity guarantees that the Fetch stage will not insert an instr
     started <= False;
     bf.clear;
  endrule

  rule decode_add
         (bf.first matches {.dpc, .i32} &&&
          toInstr(i32) matches (tagged Add {rd:.rd, ra:.ra, rb:.rb}) &&&
          (!(chk(ra) || chk(rb))));
     let new_itmpl = EAdd { rd : rd,
			    ra : rval1(ra),
			    rb : rval2(rb) };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_jz
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged Jz {cd:.cd, addr:.addr}) &&&
	  (!(chk(cd) || chk(addr))));
     let new_itmpl = EJz { cd : rval1(cd), addr : rval2(addr) };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_load
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged Load {rd:.rd, addr:.addr}) &&&
	  (!(chk(addr))));
     let new_itmpl = ELoad { rd : rd, addr : rval1(addr) };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_store
         (bf.first matches {.dpc, .i32} &&&
          toInstr(i32) matches (tagged Store {v:.v, addr:.addr}) &&&
	  (!(chk(v) || chk(addr))));
     let new_itmpl = EStore { v : rval1(v), addr : rval2(addr) };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_loadc
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged LoadC {rd:.rd, v:.v}));
     let new_itmpl = ELoadC { rd : rd, v : zeroExtend(v) };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule
  endrules;

  Rules decode_stall_rule =
   rules
      rule decode_debug (bf.first matches {.dpc, .i32});
	 $display("Stalling instr = (%d, %d)", dpc, i32);

	 // For debugging:
	 //case (toInstr(i32)) matches
	 //   tagged Add {ra:.ra, rb:.rb} : begin
	 //      $display("ra stalls: be = %b, bm = %b",
	 //               beStall(ra), bmStall(ra));
	 //      $display("rb stalls: be = %b, bm = %b",
	 //               beStall(rb), bmStall(rb));
	 //   end
	 //   tagged Jz {cd:.cd, addr:.addr} : begin
	 //      $display("Cond stalls: be = %b, bm = %b",
	 //               beStall(cd), bmStall(cd));
	 //      $display("Addr stalls: be = %b, bm = %b",
	 //               beStall(addr), bmStall(addr));
	 //   end
	 //   default: noAction;
	 //endcase

      endrule
   endrules;

  Rules decode_rules = preempts(decode_non_stall_rules, decode_stall_rule);


  // ----------------------------
  // The Execute stage

  /* ---------------------------------------------------------
     We can't use this version of the execute stage, because
     the branch not taken case clears the decode FIFO, which
     must be sequentially ordered AFTER the decode rule which
     is enqueing into the FIFO.  However the FIFO is a one
     place FIFO which allows enqueue if the other side is
     dequeing in the same cycle.  That forces that the dequeue
     happen BEFORE the enqueue.  These conflicts mean that
     decode and execute conflict.  This is acceptable in the
     case of branch not taken, but in normal operation, we want
     the pipeline to flow.  (Alternatively, we allow a branch
     delay slot, and don't clear the 1-place FIFO at all...)

     The following one-rule version of the execute stage is
     replaced with separate rules, so that the conflict of
     the branch-not-taken rule doesn't force a conflict with
     the other cases:
     ---------------------------------------------------------
     
     rule execute (bd.first matches {.epc, .instTemplate});
       case (instTemplate) matches
	  tagged EAdd {rd:.rd, ra:.va, rb:.vb} : 
	     action
	        let new_itmpl = ELoadC { rd : rd, v : va + vb };
	        be.enq(tuple2(epc, new_itmpl));
	        bd.deq;
	     endaction
	  tagged EJz {cd:.cv, addr:.av} : 
	     if (cv == 0)
	       action
		  pc <= av;
		  bd.clear;
		  bf.clear;
	       endaction
	     else
	          bd.deq;
	  default : 
	     action
	        be.enq(bd.first);
	        bd.deq;
	     endaction
       endcase
     endrule

     --------------------------------------------------------- */

  // We want a default rule which fires when the others do not.
  // Either we explicitly give that rule a condition which covers
  // all the cases not covered by the first rules, or else we
  // implement it in the following way, using "preempt":

  Rules execute_case_rules =
   rules
      rule execute_add
             (bd.first matches {.epc, .instTemplate} &&&
	      instTemplate matches (tagged EAdd {rd:.rd, ra:.va, rb:.vb}));
	 let new_itmpl = ELoadC { rd : rd, v : va + vb };
	 be.enq(tuple2(epc, new_itmpl));
	 bd.deq;
      endrule

      rule execute_jz_taken
             (bd.first matches {.epc, .instTemplate} &&&
	      instTemplate matches (tagged EJz {cd:.cv, addr:.av}) &&&
	      cv == 0);
	 pc <= av;
	 bd.clear;
	 bf.clear;
      endrule

      rule execute_jz_not_taken
             (bd.first matches {.epc, .instTemplate} &&&
	      instTemplate matches (tagged EJz {cd:.cv, addr:.av}) &&&
	      cv != 0);
	 bd.deq;
      endrule
   endrules;

  Rules execute_default_rule =
   rules
      rule execute_default;
	 be.enq(bd.first);
	 bd.deq;
      endrule
   endrules;

  // Any rule in execute_case_rules preempts the default case
  Rules execute_rules = preempts(execute_case_rules, execute_default_rule);

  // The execute stage should take precedence over the decode stage
  // (only the execute_jz_not_taken rule should conflict)

  // This adds conflicts where none should be.
  //   addRules(preempts(execute_rules, decode_rules));
  addRules(execute_rules);
  addRules(decode_rules);


  // ----------------------------
  // The memory stage

  rule mem_rule (be.first matches {.mpc, .instTemplate});
     be.deq;
     case (instTemplate) matches
	tagged ELoad {rd:.rd, addr:.addr} :
	   begin
	      let new_itmpl = ELoadC { rd : rd, v : dataMem.get(addr) };
	      bm.enq(tuple2(mpc, new_itmpl));
	   end
	tagged EStore {v:.v, addr:.addr} :
	   dataMem.put(addr, v);
	default :
	   bm.enq(be.first);
     endcase
  endrule

  // ----------------------------
  // The write-back stage

  rule wb_rule (bm.first matches {.wpc, .instTemplate});
     bm.deq;
     case (instTemplate) matches
	tagged ELoadC {rd:.rd, v:.v} :
	   rf.write(rd, v);
	default :  noAction;
     endcase
  endrule

  // ----------------------------
  // Exported interfaces

  interface imem = instrMem;
  interface dmem = dataMem;

  method start() ;
    action
      started <= True;
    endaction
  endmethod

  method done = !started && !bd.notEmpty && !be.notEmpty && !bm.notEmpty;
   
endmodule: mkFiveStageCPUBypassPreFIFO

