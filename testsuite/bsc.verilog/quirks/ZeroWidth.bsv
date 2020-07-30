
import FIFOF::*;
//import FIFO::*;
import Vector::*;

typedef 1 NTHREADS;
typedef Bit#(TLog#(NTHREADS)) TypeThreadNum;
typedef Maybe#(TypeThreadNum) TypeMaybeThreadNum;
typedef Vector#(NTHREADS, Bool) TypeBoolVec;

function TypeThreadNum advanceThreadNum(TypeThreadNum k);
  return ((k == (fromInteger(valueof(NTHREADS) - 1))) ? 0 : (k+1));
endfunction

(*noinline*)
function Maybe#(TypeThreadNum) selectThread(TypeBoolVec legits,
                                            TypeThreadNum startAt);
  Bool going = True; TypeThreadNum j = startAt; Maybe#(TypeThreadNum) r =
tagged Invalid;
  for (Integer i=0; i<valueof(NTHREADS); i=i+1)
     if (going && legits[j]) begin going = False; r = tagged Valid j; end
     else j = advanceThreadNum(j);
  return r;
endfunction


(*noinline*)
function Tuple2#(Bool,TypeThreadNum) selectThread2(TypeBoolVec legits,
                                            TypeThreadNum startAt);
   Bool going = True; 
   TypeThreadNum j = startAt; 
   TypeThreadNum r = 0;
  for (Integer i=0; i<valueof(NTHREADS); i=i+1)
     if (going && legits[j]) begin going = False; r = j; end
     else j = advanceThreadNum(j);
  return tuple2( !going, r ) ;
endfunction

(* synthesize *)
module mkTst(Empty);
  Reg#(TypeThreadNum) tnum <- mkReg(0);

  rule go;
     TypeBoolVec eligible = replicate(True);
     TypeMaybeThreadNum mt = selectThread(eligible, tnum);
     let x = selectThread2(eligible, tnum);
     $display("selected valid = %d,  tnum = %d", isValid(mt), fromMaybe(0,mt), tpl_1(x), tpl_2(x));
     $stop(0);
  endrule

endmodule: mkTst

