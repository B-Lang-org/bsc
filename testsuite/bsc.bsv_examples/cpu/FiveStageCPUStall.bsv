/*----------------------------------------------------------------------------

FiveStageCPUStall

This is a naively written five-stage CPU w/stall.  Look at
FiveStageCPUStallV2 for a version which reduces the data in the
buffers between the stages (reducing the size of the buffers as
well as greatly reducing the logic needed for stalling).

FiveStageCPUBypass and FiveStageCPUBypassPreFIFO investigate
extending this design to bypass rather than stall.

-----------------------------------------------------------------------------*/

import RegFile::*;
import FIFO::*;
import FindFIFO2::*;

// Data type for naming the registers (equivalent to a 5-bit vector)
// Note that in this architecture, register R0 reads 0 and discards writes

typedef enum
  { R0 , R1 , R2 , R3 , R4 , R5 , R6 , R7 ,
    R8 , R9 , R10, R11, R12, R13, R14, R15,
    R16, R17, R18, R19, R20, R21, R22, R23,
    R24, R25, R26, R27, R28, R29, R30, R31 } RName deriving (Bits, Eq);
  // typedef Bit#(5) RName;

typedef Bit#(32) Ia;   // Instruction address
typedef Bit#(32) Value;
typedef Bit#(10) Const;

typedef RName Src;
typedef RName Dest;
typedef RName Cond;
typedef RName Addr;
typedef RName Val;


// --------------------------------------------------------
// The data type for the instruction set

typedef union tagged {
    struct { Dest rd; Src   ra; Src rb; } Add;
    struct { Cond cd; Addr  addr; }       Jz;
    struct { Dest rd; Addr  addr; }       Load;
    struct { Val  v;  Addr  addr; }       Store;
    struct { Dest rd; Const v; }          LoadC;
    void                                  Halt;
} Instr deriving (Bits);


// --------------------------------------------------------
// The data type for the state between stages

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

  // The array needs to have conflict-free writing and reading.
  // The stalling mechanism will guarantee that we never try to
  // read and write from the same register in the same clock cycle.
  // The reason that this needs to be conflict free is to prevent
  // a sequential conflict between the write-back stage (writing
  // to the array) and the decode stage (reading from the array).
  // The stages already have to be ordered in one direction because
  // of the buffers are one-place FIFOS with simultaneous enq/deq,
  // so the deq side must happen first, to make room for the enq.
  // Adding the reverse requirement (read the array before writing)
  // causes a conflict, and some stages would never be able to fire
  // in the same cycle.  This is not acceptable behavior.
   
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

module mkFiveStageCPUStall(CPU);

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
  // It can be probed for stalling
  FindFIFO#(Tuple2#(Ia, InstTemplate)) bd();
  mkFindFIFO the_bd(bd);

  // Buffer after the execute stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFO#(Tuple2#(Ia, InstTemplate)) be();
  mkFindFIFO the_be(be);

  // Buffer after the memory stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFO#(Tuple2#(Ia, InstTemplate)) bm();
  mkFindFIFO the_bm(bm);

  // The CPU leaves reset in an idle state and does not start fetching
  // instructions until this register is set to True.
  Reg#(Bool) started();
  mkReg#(False) the_started(started);

  // ----------------------------
  // Convenience functions
   
  // A function which describes the stall condition:
  // Given a register which an incoming instruction wants to
  // read ("r") and an entry in any of the buffer stages
  // (that is, a pair containing the instr location and the
  // instr template), this function returns True if the buffer
  // entry is scheduled to write a value to that register.
  // Note: The function only returns True or False, which is
  // enough information to stall the pipeline.  In order to
  // implement bypassing, the function would need to also return
  // a value for the register if it has been computed.
  // Also note: The function doesn't check whether rd == R0.
  // R0's value never changes, so there is never a need to stall.

  function findf(r, pci);
    case (tpl_2(pci)) matches
       tagged EAdd   {rd:.rd} :  return (r == rd) ;
       tagged EJz    {}       :  return (False)   ;
       tagged ELoad  {rd:.rd} :  return (r == rd) ;
       tagged EStore {}       :  return (False)   ;
       tagged ELoadC {rd:.rd} :  return (r == rd) ;
    endcase
  endfunction: findf

  // Aliases for the lookup in each FIFO
  function bdStall(r); return bd.find(findf(r)); endfunction
  function beStall(r); return be.find(findf(r)); endfunction
  function bmStall(r); return bm.find(findf(r)); endfunction

  // A single function which performs the stall check on all FIFOs
  function chk(r); return (bdStall(r) || beStall(r) || bmStall(r)); endfunction

  // Aliases for looking up a register's value in the register file
  function rval1(r); return rf.read1(r); endfunction
  function rval2(r); return rf.read2(r); endfunction

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
	 $display("Stalling instruction from pc %d", dpc);
      endrule
   endrules;

  Rules decode_rules = preempts(decode_non_stall_rules, decode_stall_rule);
   
  addRules(decode_rules);


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

  addRules(execute_rules);


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
   
endmodule: mkFiveStageCPUStall

