package PPC_BranchPredictor;

/******************************************************************************/
/*                       PPC_BranchPredictor                                  */
/*                                                                            */
/*  A simple BTB with 4 entries and a one-bit prediction scheme. Available    */
/* for processors which do not want an in-depth model of a branch predictor.  */
/*                                                                            */
/*                                                                            */
/* Parameters:                                                                */
/*  Address Width: Variable (Needs Arith, Eq, Bits)                           */
/*                                                                            */
/******************************************************************************/

import PPC_Datatypes::*;

import List::*;
import FIFO::*;
  
interface BranchPredictor#(type iaddr_t);

    //XXX Convert back when Bug 247 is dead
    method Action                   branch_Action(iaddr_t x);
    method Tuple2#(iaddr_t, Bool)   branch_Value(iaddr_t x);

    method Action update(BranchPredUpdate#(iaddr_t) x);
    method Action flush();
endinterface


// This uses a simple 2 bit predictor to determine which of two tables
// (Taken / NotTaken) should be indexed for use.

typedef struct
{
  Reg#(iaddr_t) itag;
  Reg#(iaddr_t) pred;
} 
  TableEntry#(type iaddr_t);

(* synthesize *)
module mkBranchPred_64 (BranchPredictor#(Bit#(64)));

    BranchPredictor#(Bit#(64)) bp <- mkBranchPred();

    method Action                   branch_Action(Bit#(64) x);
      bp.branch_Action(x);
    endmethod
    
    method Tuple2#(Bit#(64), Bool)   branch_Value(Bit#(64) x);
      return (bp.branch_Value(x));
    endmethod
    
    method Action update(BranchPredUpdate#(Bit#(64)) x);
      bp.update(x);
    endmethod
    
    method Action flush();
      bp.flush();
    endmethod
  
endmodule

module mkBranchPred (BranchPredictor#(iaddr_t))
          provisos (Bits#(iaddr_t, sz), Eq#(iaddr_t), Arith#(iaddr_t));
	 
  let table_sz = 4;

  //XXX Should be generalized so I scale with table_sz
  function Bit#(2) getIndex(iaddr_t pc);
    return (pack(pc)[3:2]);
  endfunction

  function Bool tagMatched(iaddr_t t, TableEntry#(iaddr_t) tEntry);
    return (tEntry.itag._read == t);
  endfunction

  // XXX Should I be a one bit prd given the delay in update?
  Reg#(bit[1:0]) twoBitPred <- mkReg(0);

  module mkTableEntry#(Integer i) (TableEntry#(iaddr_t));
     let itag <- mkReg(0);
     let pred <- mkReg(4);
     return(TableEntry { itag : itag, pred : pred});
  endmodule

  List#(TableEntry#(iaddr_t)) tEntries;
  tEntries <- mapM(mkTableEntry, upto(0, table_sz - 1));

  List#(TableEntry#(iaddr_t)) ntEntries;
  ntEntries <- mapM(mkTableEntry, upto(0, table_sz - 1));

  //XXX One day bugs 247 & 86 will be fixed and these can be merged

  method Tuple2#(iaddr_t, Bool) branch_Value (iaddr_t ia);
     let tbl   = ((twoBitPred[1] == 1) ? tEntries: ntEntries);
     let entry = (select(tbl, getIndex(ia)));

     return ((tagMatched(ia, entry) ?
              tuple2((entry.pred)._read,twoBitPred == 1)
             :tuple2(ia + 4, False)));
  endmethod: branch_Value

  method Action branch_Action (iaddr_t ia);
     let tbl   = ((twoBitPred[1] == 1) ? tEntries: ntEntries);
     let entry = (select(tbl, getIndex(ia)));
     noAction;  
  endmethod: branch_Action

  method update (BranchPredUpdate#(iaddr_t) bpred);
     action
        //update predictor
        //twoBitPred <= (takenp)? 
        //               ((twoBitPred == 2'b11)? 2'b11 : twoBitPred + 1):
        //               ((twoBitPred == 2'b00)? 2'b00 : twoBitPred - 1);
       

       Bool choice = bpred.taken;

       Bit#(2) first_path = 
          case (twoBitPred)
	    2'b00:
	      return 2'b11;
	    2'b01:
	      return 2'b00;
	    2'b10:
	      return 2'b11;
	    2'b11:
	      return 2'b11;
	  endcase; // case(twoBitPred)

       Bit#(2) second_path = 
         case (twoBitPred)
	    2'b00:
	      return 2'b01;
	    2'b01:
	      return 2'b01;
	    2'b10:
	      return 2'b01;
	    2'b11:
	      return 2'b10;
         endcase;


       twoBitPred <= (choice?first_path:second_path);

        let tbl   = (bpred.pred) ? tEntries: ntEntries;
        let entry = select(tbl, getIndex(bpred.ia));

        (entry.itag) <= bpred.ia;
        (entry.pred) <= bpred.real_next_ia;
        
     endaction
  endmethod: update
  
  // This should probably do something reasonable instead of just nothing.
  method flush();
    action
      noAction;
    endaction
  endmethod: flush

endmodule

endpackage
