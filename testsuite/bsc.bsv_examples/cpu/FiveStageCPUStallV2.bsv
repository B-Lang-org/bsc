/*----------------------------------------------------------------------------

FiveStageCPUStallV2

This version of the five-stage CPU w/stall differs from the previous
version in the type-definition of the buffers between the stages.
This version defines structures which conserve bits.  The structures
in this version also vectorize the pipeline control into a struct data
type (rather than tagged union type), which allows new instructions
which are combinations of existing instructions to be added without
needing to add more bits (for the new tags).

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
// The data types for the state between stages

// ALU operations
typedef enum { AddOp } ALUOp
    deriving (Eq, Bits);

// Branch operations
typedef enum { JzOp } BranchOp
    deriving (Eq, Bits);

// Memory operations
typedef enum { LoadOp, StoreOp } MemOp
    deriving (Eq, Bits);


// The state after the decode stage
typedef struct {
    Maybe#(ALUOp)    alu_op;
    Maybe#(BranchOp) br_op;
    Maybe#(MemOp)    mem_op;
    // Destination register in which to load a value from memory
    // or record an ALU computation, if value is to be written to
    // the register file.
    Maybe#(Dest)  rd;
    // For ALU ops, these are the arguments,
    // for memory operations with an argument, use ra
    Value ra;
    Value rb;
    // Address for memory or branch operations
    Value addr;
} BDdata  // state in the buffer after the decode stage
    deriving (Bits);


// The state after the execute stage
typedef struct {
    Maybe#(MemOp) mem_op;
    // Destination register in which to load a value from memory
    // or record an ALU computation
    Maybe#(Dest) rd;
    // Result of computation
    Value v;
    // Address for memory operations
    Value addr;
} BEdata  // state in the buffer after the execute stage
    deriving (Bits);


// The state after the memory stage
typedef struct {
    Dest rd;  // register to write back to
    Value v;  // value to be written
} BMdata  // state in the buffer after the execute stage
    deriving (Bits);


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

  // The array needs to have conflict-free writing and reading.
  // See comment in FiveStageCPUStall.bsv

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
  FindFIFO#(Tuple2#(Ia, BDdata)) bd();
  mkFindFIFO the_bd(bd);

  // Buffer after the execute stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFO#(Tuple2#(Ia, BEdata)) be();
  mkFindFIFO the_be(be);

  // Buffer after the memory stage
  // Contains: pc, instr template
  // It can be probed for stalling
  FindFIFO#(Tuple2#(Ia, BMdata)) bm();
  mkFindFIFO the_bm(bm);

  // The CPU leaves reset in an idle state and does not start fetching
  // instructions until this register is set to True.
  Reg#(Bool) started();
  mkReg#(False) the_started(started);

  // ----------------------------
  // Convenience functions
   
  // Functions which describe the stall condition:
  // Given a register which an incoming instruction wants to
  // read ("r") and an entry in any of the buffer stages
  // (that is, a pair containing the instr location and the
  // instr template), this function returns True if the buffer
  // entry is scheduled to write a value to that register.
  // Note: The functions only return True or False, which is
  // enough information to stall the pipeline.  In order to
  // implement bypassing, the function would need to also return
  // a value for the register if it has been computed.
  // Also note: The function doesn't check whether rd == R0.
  // R0's value never changes, so there is never a need to stall.

  function findf_bd(r, pci);
    BDdata tmpl = tpl_2(pci);
    case (tmpl.rd) matches
       tagged Valid .rd :  return (r == rd) ;
       tagged Invalid  :  return (False);
    endcase
  endfunction: findf_bd

  function findf_be(r, pci);
    BEdata tmpl = tpl_2(pci);
    case (tmpl.rd) matches
       tagged Valid .rd :  return (r == rd) ;
       tagged Invalid  :  return (False);
    endcase
  endfunction: findf_be

  function findf_bm(r, pci);
    BMdata tmpl = tpl_2(pci);
    return (r == tmpl.rd);
  endfunction: findf_bm

  // Aliases for the lookup in each FIFO
  function bdStall(r); return bd.find(findf_bd(r)); endfunction
  function beStall(r); return be.find(findf_be(r)); endfunction
  function bmStall(r); return bm.find(findf_bm(r)); endfunction

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
     let new_itmpl = BDdata { alu_op : Valid(AddOp),
			      ra : rval1(ra),
			      rb : rval2(rb),
			      rd : Valid(rd),
			      br_op : Invalid,
			      mem_op : Invalid,
			      addr : ? };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_jz
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged Jz {cd:.cd, addr:.addr}) &&&
	  (!(chk(cd) || chk(addr))));
     let new_itmpl = BDdata { br_op  : Valid(JzOp),
			      ra     : rval1(cd),
			      addr   : rval2(addr),
			      mem_op : Invalid,
			      alu_op : Invalid,
			      rb     : ?,
			      rd     : Invalid };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_load
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged Load {rd:.rd, addr:.addr}) &&&
	  (!(chk(addr))));
     let new_itmpl = BDdata { mem_op : Valid(LoadOp),
			      rd : Valid(rd),
			      addr : rval2(addr),
			      br_op : Invalid,
			      alu_op : Invalid,
			      ra : ?,
			      rb : ? };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_store
         (bf.first matches {.dpc, .i32} &&&
          toInstr(i32) matches (tagged Store {v:.v, addr:.addr}) &&&
	  (!(chk(v) || chk(addr))));
     let new_itmpl = BDdata { mem_op : Valid(StoreOp),
			      ra : rval1(v),
			      addr : rval2(addr),
			      rd : Invalid,
			      br_op : Invalid,
			      alu_op : Invalid,
			      rb : ? };
     bd.enq(tuple2(dpc, new_itmpl));
     bf.deq;
  endrule

  rule decode_loadc
         (bf.first matches {.dpc, .i32} &&&
	  toInstr(i32) matches (tagged LoadC {rd:.rd, v:.v}));
     let new_itmpl = BDdata { alu_op : Valid(AddOp), // add 0 to v
			      rd : Valid(rd),
			      ra : zeroExtend(v),
			      rb : rval2(R0),
			      br_op : Invalid,
			      mem_op : Invalid,
			      addr : ? };
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
       // Simulate an ALU stage, separate from the branch stage,
       // without actually introducing a new pipeline stage:

       BDdata new_tmpl = instTemplate;

       case (instTemplate.alu_op) matches
	  tagged Invalid : noAction;

	  tagged Valid .alu_op :
	     begin
	        Value va = instTemplate.ra;
	        Value vb = instTemplate.rb;
	        Value vc;
	        case (alu_op) matches
		   AddOp : vc = va + vb;
	        endcase
	        new_tmpl.ra = vc;
	     end
       endcase

       case (new_tmpl.br_op) matches
	  tagged Invalid : bd.deq;

	  tagged Valid (JzOp) :
	     if (new_tmpl.ra == 0)
	       action
		  pc <= new_tmpl.addr;
		  bd.clear;
		  bf.clear;
	       endaction
	     else
	          bd.deq;
       endcase

       // Does the instruction need to continue to the next stages?
       // (If this adds extra unneeded logic, remove it.)
       if (isValid(new_tmpl.mem_op) || isValid(new_tmpl.rd)) begin
	  let be_data = BEdata { mem_op : new_tmpl.mem_op,
		                 rd :     new_tmpl.rd,
		                 v :      new_tmpl.ra,
		                 addr:    new_tmpl.addr };
	  be.enq(tuple2(epc, be_data));
       end
     endrule

     --------------------------------------------------------- */

   // Simulate an ALU stage, separate from the branch stage,
   // without actually introducing a new pipeline stage.
   
   // Define what the new va would be after computing the operation
   // part of the instruction:
   function Value execute_vc(BDdata instTemplate);
      case (instTemplate.alu_op) matches
	 tagged Invalid : return instTemplate.ra;
	 tagged Valid .alu_op :
	    begin
	       Value va = instTemplate.ra;
	       Value vb = instTemplate.rb;
	       Value vc;
	       case (alu_op) matches
		  AddOp : vc = va + vb;
	       endcase
	       return vc;
	    end
      endcase
   endfunction

  Rules execute_br_taken_rule =
   rules
      rule execute_branch_taken
             (bd.first matches {.epc, .instTemplate} &&&
              instTemplate.br_op matches (tagged Valid (JzOp)) &&&
              execute_vc(instTemplate) == 0);
	 pc <= instTemplate.addr;
	 bd.clear;
	 bf.clear;
      endrule
   endrules;

  Rules execute_default_rule =
   rules
      // This covers branch not taken, alu op without a branch, and
      // any other instruction.
      rule execute_default
             (bd.first matches {.epc, .tmpl});
	 bd.deq;
	 // One could remove the surrounding if-statement and always
	 // let the instruction pass through, as a no-op.  This would
	 // save logic.
	 if (isValid(tmpl.mem_op) || isValid(tmpl.rd)) begin
	    let be_data = BEdata { mem_op : tmpl.mem_op,
		                   rd :     tmpl.rd,
		                   v :      execute_vc(tmpl),
		                   addr:    tmpl.addr };
	    be.enq(tuple2(epc, be_data));
	 end
      endrule
   endrules;

  Rules execute_rules = preempts(execute_br_taken_rule, execute_default_rule);

  addRules(execute_rules);

   
  // ----------------------------
  // The memory stage

  rule mem_rule (be.first matches {.mpc, .instTemplate});
     be.deq;

     BEdata new_tmpl = instTemplate;
 
     case (instTemplate.mem_op) matches
	tagged Invalid : noAction;
	   
	tagged Valid (LoadOp) :
	   new_tmpl.v = dataMem.get(instTemplate.addr);

	tagged Valid (StoreOp) :
	   dataMem.put(instTemplate.addr, instTemplate.v);
     endcase

     // Does the instruction need to continue to the next stages?
     // (If this adds extra unneeded logic, change the buffer to
     // continue to store rd as a Maybe and remove this logic.)
     if (isValid(new_tmpl.rd)) begin
	let bm_data = BMdata { rd :  validValue(new_tmpl.rd),
		               v :   new_tmpl.v };
	bm.enq(tuple2(mpc, bm_data));
     end

  endrule

  // ----------------------------
  // The write-back stage

  rule wb_rule (bm.first matches {.wpc, .instTemplate});
     bm.deq;
     rf.write(instTemplate.rd, instTemplate.v);
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

