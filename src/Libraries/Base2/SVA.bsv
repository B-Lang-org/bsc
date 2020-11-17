package SVA;
import List::*;

//========
/*
MISSING:

mkSeqDelayUnbound
mkSeqDelayConst
mkSeqDelayRange

*/
// SVA functions

function a valueFunctionSVA (b x, function a cf(b y, b z))
   provisos (Bits#(b,sb));
   let c0 = clockOf(x);
   let c = (c0!=noClock) ? c0 :
           error("arguments of SVA value functions cannot be clocked by noClock");
   let r = noReset;
   let oldVal = primBuildModule(Prelude::primGetName(valueFunctionSVAint), c, r,
				module#(b);
				   Reg#(b) oldValReg <- mkRegU;
				   rule upd;
				      oldValReg <= x;
				   endrule
				return oldValReg;
				endmodule);
   return (cf(x, oldVal));
endfunction

function b \$sampled (b x)
   provisos (Bits#(b,sb));
   function old(x1,x2) = (x2);
      return (valueFunctionSVA(x, old));
endfunction

function Bool \$rose (b x)
   provisos (Bits#(b,sb));
   function gt(x1,x2) = (x1>x2);
      return (valueFunctionSVA(pack(x)[0], gt));
endfunction

function Bool \$fell (b x)
   provisos (Bits#(b,sb));
   function lt(x1,x2) = (x1<x2);
      return (valueFunctionSVA(pack(x)[0], lt));
endfunction

function Bool \$stable (b x)
   provisos (Bits#(b,sb));
      return (valueFunctionSVA(pack(x), \== ));
endfunction

function Bool \$onehot (b x)
   provisos (Bits#(b,sb));
   let y = pack(x);
   return (y!=0 && (y&(y-1))==0);
endfunction

function Bool \$onehot0 (b x)
   provisos (Bits#(b,sb));
   return ($onehot(invert(pack(x))));
endfunction

function Bool \$isunknown (b x) provisos (Bits#(b,sb));
   return False;
endfunction

function UInt#(lsb) \$countones (b x)
   provisos (Bits#(b,sb), Log#(TAdd#(1,sb),lsb),
	     Add#(1,a,lsb));
   return countOnes(pack(x));
endfunction

// =====

typedef enum {
  SeqFail, SeqPending, SeqHold, SeqHoldStrong} SeqRes deriving (Eq, Bits);

interface Sequence;
    method Bool running();
    method ActionValue#(SeqRes) advance();
endinterface: Sequence

module mkSeqVoid(Sequence);
  method advance() ; actionvalue return SeqFail; endactionvalue
  endmethod: advance
  method running() ;   return False;
  endmethod: running
endmodule: mkSeqVoid

module mkSeqTrue(Sequence);
  method advance() ; actionvalue return SeqHoldStrong; endactionvalue
  endmethod: advance
  method running() ;   return False;
  endmethod: running
endmodule: mkSeqTrue

/*
(* noinline *)
function SeqRes doSeqExpr(Bool b);
  return (b ? SeqHoldStrong : SeqFail);
endfunction: doSeqExpr
*/

(*always_ready*)
interface Wrap1;
   method SeqRes f(Bool b);
endinterface

(*synthesize*)
module mkDoSeqExpr(Wrap1);
   method SeqRes f(Bool b);
      return (b ? SeqHoldStrong : SeqFail);
   endmethod
endmodule

module mkSeqExpr#(Bool dynbool)(Sequence);
  let md <- mkDoSeqExpr;
  let doSeqExpr =  md.f;
  method running() ;   return False;
  endmethod: running
  method advance() ;
    actionvalue
      return doSeqExpr(dynbool);
    endactionvalue
  endmethod: advance
endmodule: mkSeqExpr

module mkSeqAsgn#(Action dynaction)(Sequence);
  method advance() ;
    actionvalue
      dynaction;
      return SeqHoldStrong;
    endactionvalue
  endmethod: advance
  method running() ;   return False;
  endmethod: running
endmodule: mkSeqAsgn

/*
(* noinline *)
function Tuple3#(Bool, Bool, SeqRes) doSeqConcatA(SeqRes r);
  return (begin case (r) matches
		tagged SeqFail :  (tuple3(False, False, SeqFail));
		tagged SeqPending :  (tuple3(True, False, SeqPending));
		tagged SeqHold :  (tuple3(True, False, SeqPending));
		tagged SeqHoldStrong :  (tuple3(False, True, SeqPending));
		endcase
	  end);
endfunction: doSeqConcatA
*/

(*always_ready*)
interface Wrap2;
   method Tuple3#(Bool, Bool, SeqRes) f(SeqRes r);
endinterface

(*synthesize*)
module mkDoSeqConcatA(Wrap2);
   method Tuple3#(Bool, Bool, SeqRes) f(SeqRes r);
      return (begin case (r) matches
		       tagged SeqFail :  (tuple3(False, False, SeqFail));
		       tagged SeqPending :  (tuple3(True, False, SeqPending));
		       tagged SeqHold :  (tuple3(True, False, SeqPending));
		       tagged SeqHoldStrong :  (tuple3(False, True, SeqPending));
		    endcase
	      end);
   endmethod
endmodule

/*
(* noinline *)
function Tuple3#(Bool, Bool, SeqRes) doSeqConcatB(SeqRes r);
  return (begin case (r) matches
		tagged SeqFail :  (tuple3(False, False, SeqFail));
		tagged SeqPending :  (tuple3(False, True, SeqPending));
		tagged SeqHold :  (tuple3(False, True, SeqHold));
		tagged SeqHoldStrong :  (tuple3(False, False, SeqHoldStrong));
		endcase
	  end);
endfunction: doSeqConcatB
*/

(*synthesize*)
module mkDoSeqConcatB(Wrap2);
   method Tuple3#(Bool, Bool, SeqRes) f(SeqRes r);
      return (begin case (r) matches
		       tagged SeqFail :  (tuple3(False, False, SeqFail));
		       tagged SeqPending :  (tuple3(False, True, SeqPending));
		       tagged SeqHold :  (tuple3(False, True, SeqHold));
		       tagged SeqHoldStrong :  (tuple3(False, False, SeqHoldStrong));
		    endcase
	      end);
   endmethod
endmodule

module mkSeqConcat#(module#(Sequence) m1, module#(Sequence) m2)(Sequence);
  let ma <- mkDoSeqConcatA;
  let doSeqConcatA = ma.f;
  let mb <- mkDoSeqConcatB;
  let doSeqConcatB = mb.f;
  let s1 <- m1;
  let s2 <- m2;
  let run_1 <- mkReg(False);
  let run_2 <- mkReg(False);
  method running() ;   return (run_1 || run_2);
  endmethod: running
  method advance() ;
    actionvalue
      let {run_1a,run_2a,res} <- run_1 || !(run_1) && !(run_2) ?
				     (actionvalue
					let r <- s1.advance;
					return(doSeqConcatA(r));
				      endactionvalue)
				 :   (actionvalue
					let r2 <- s2.advance;
					return(doSeqConcatB(r2));
				      endactionvalue);
      run_1 <= run_1a;
      run_2 <= run_2a;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkSeqConcat

/*
(* noinline *)
function Tuple3#(Bool, Bool, SeqRes) doSeqFuseA(SeqRes r);
  return (begin case (r) matches
		tagged SeqFail :  (tuple3(False, False, SeqFail));
		tagged SeqPending :  (tuple3(True, False, SeqPending));
		tagged SeqHold :  (tuple3(True, False, SeqPending));
		tagged SeqHoldStrong :  (tuple3(False, True, SeqPending));
		endcase
	  end);
endfunction: doSeqFuseA
*/

(*synthesize*)
module mkDoSeqFuseA(Wrap2);
   method Tuple3#(Bool, Bool, SeqRes) f(SeqRes r);
      return (begin case (r) matches
		       tagged SeqFail :  (tuple3(False, False, SeqFail));
		       tagged SeqPending :  (tuple3(True, False, SeqPending));
		       tagged SeqHold :  (tuple3(True, False, SeqPending));
		       tagged SeqHoldStrong :  (tuple3(False, True, SeqPending));
		    endcase
	      end);
   endmethod
endmodule

module mkSeqFuse#(module#(Sequence) m1, module#(Sequence) m2)(Sequence);
  let mf <- mkDoSeqFuseA;
  let doSeqFuseA = mf.f;
  let mb <- mkDoSeqConcatB;
  let doSeqConcatB = mb.f;
  let s1 <- m1;
  let s2 <- m2;
  let run_1 <- mkReg(False);
  let run_2 <- mkReg(False);
  method running() ;   return (run_1 || run_2);
  endmethod: running
  method advance() ;
    actionvalue
      let {run_1a,start,r1} <- run_1 || !(run_1) && !(run_2) ?
				   (actionvalue
				      let r <- s1.advance;
				      return(doSeqFuseA(r));
				    endactionvalue)
       :   (actionvalue
	       return tuple3(False, False, SeqPending);
	    endactionvalue);
      let {.*,run_2a,res} <- run_2 || start ?
				 (actionvalue
				    let r <- s2.advance;
				    return(doSeqConcatB(r));
				  endactionvalue)
       :  (actionvalue
	      return tuple3(False, False, r1);
	   endactionvalue);
      run_1 <= run_1a;
      run_2 <= run_2a;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkSeqFuse

/*
(* noinline *)
function Bool seqRunning(SeqRes r);
  return (begin case (r) matches
		tagged SeqFail :  (False);
		tagged SeqPending :  (True);
		tagged SeqHold :  (True);
		tagged SeqHoldStrong :  (False);
		endcase
	  end);
endfunction: seqRunning
*/

(*always_ready*)
interface Wrap3;
   method Bool f(SeqRes r);
endinterface

(*synthesize*)
module mkSeqRunning(Wrap3);
   method Bool f(SeqRes r);
      return (begin case (r) matches
		       tagged SeqFail :  (False);
		       tagged SeqPending :  (True);
		       tagged SeqHold :  (True);
		       tagged SeqHoldStrong :  (False);
		    endcase
	      end);
   endmethod
endmodule

/*
(* noinline *)
function SeqRes doSeqOrRes(Bool run_1, Bool run_2, SeqRes res_l, SeqRes res_r);
  return ((res_l == SeqHoldStrong && res_r == SeqHoldStrong ?
	       SeqHoldStrong
	   :   ((res_l == SeqHoldStrong) && !(run_2) && run_1 ?
		    SeqHoldStrong
		:   (!(run_1) && (res_r == SeqHoldStrong) && run_2 ?
			 SeqHoldStrong
		     :   (res_l == SeqHoldStrong || res_r == SeqHoldStrong ?
			      SeqHold
			  :   (res_l == SeqHold || res_r == SeqHold ?
				   SeqHold
			       :   (res_l == SeqFail && res_r == SeqFail ? SeqFail : SeqPending)))))));
endfunction: doSeqOrRes
*/

(*always_ready*)
interface Wrap4;
   method SeqRes f(Bool run_1, Bool run_2, SeqRes res_l, SeqRes res_r);
endinterface

(*synthesize*)
module mkDoSeqOrRes(Wrap4);
   method SeqRes f(Bool run_1, Bool run_2, SeqRes res_l, SeqRes res_r);
      return ((res_l == SeqHoldStrong && res_r == SeqHoldStrong ?
	       SeqHoldStrong
	       :   ((res_l == SeqHoldStrong) && !(run_2) && run_1 ?
		    SeqHoldStrong
		    :   (!(run_1) && (res_r == SeqHoldStrong) && run_2 ?
			 SeqHoldStrong
			 :   (res_l == SeqHoldStrong || res_r == SeqHoldStrong ?
			      SeqHold
			      :   (res_l == SeqHold || res_r == SeqHold ?
				   SeqHold
				   :   (res_l == SeqFail && res_r == SeqFail ? SeqFail : SeqPending)))))));
   endmethod
endmodule

module mkSeqOr#(module#(Sequence) m1, module#(Sequence) m2)(Sequence);
  let msr1 <- mkSeqRunning;
  let seqRunning1 = msr1.f;
  let msr2 <- mkSeqRunning;
  let seqRunning2 = msr2.f;
  let mdsr <- mkDoSeqOrRes;
  let doSeqOrRes = mdsr.f;
  let s1 <- m1;
  let s2 <- m2;
  let run_1 <- mkReg(False);
  let run_2 <- mkReg(False);
  method running() ;   return (run_1 || run_2);
  endmethod: running
  method advance() ;
    actionvalue
      let {run_1a,res_l} <- !(run_1) && !(run_2) || run_1 ?
				(actionvalue
				   let r <- s1.advance;
				   return(tuple2(seqRunning1(r), r));
				 endactionvalue)
       :   actionvalue
	      return tuple2(False, SeqPending);
	   endactionvalue;
      let {run_2a,res_r} <- !(run_1) && !(run_2) || run_2 ?
				(actionvalue
				   let r2 <- s2.advance;
				   return(tuple2(seqRunning2(r2), r2));
				 endactionvalue)
       :   actionvalue
	      return tuple2(False, SeqPending);
	   endactionvalue;
      run_1 <= run_1a;
      run_2 <= run_2a;
      return(doSeqOrRes(run_1, run_2, res_l, res_r));
    endactionvalue
  endmethod: advance
endmodule: mkSeqOr

/*
(* noinline *)
function SeqRes doSeqIntersectRes(SeqRes res_l, SeqRes res_r);
  return ((res_l == SeqHoldStrong && res_r == SeqHoldStrong ?
	       SeqHoldStrong
	   :   (res_l == SeqHoldStrong && res_r == SeqHold ?
		    SeqHoldStrong
		:   (res_l == SeqHold && res_r == SeqHoldStrong ?
			 SeqHoldStrong
		     :   (res_l == SeqHold && res_r == SeqHold ?
			      SeqHold
			  :   (res_l == SeqFail || res_r == SeqFail ? SeqFail : SeqPending))))));
endfunction: doSeqIntersectRes
*/

(*always_ready*)
interface Wrap5;
   method SeqRes f(SeqRes res_l, SeqRes res_r);
endinterface

(*synthesize*)
module mkDoSeqIntersectRes(Wrap5);
   method SeqRes f(SeqRes res_l, SeqRes res_r);
      return ((res_l == SeqHoldStrong && res_r == SeqHoldStrong ?
	       SeqHoldStrong
	       :   (res_l == SeqHoldStrong && res_r == SeqHold ?
		    SeqHoldStrong
		    :   (res_l == SeqHold && res_r == SeqHoldStrong ?
			 SeqHoldStrong
			 :   (res_l == SeqHold && res_r == SeqHold ?
			      SeqHold
			      :   (res_l == SeqFail || res_r == SeqFail ? SeqFail : SeqPending))))));
   endmethod
endmodule

module mkSeqIntersect#(module#(Sequence) m1, module#(Sequence) m2)(Sequence);
  let msr1 <- mkSeqRunning;
  let seqRunning1 = msr1.f;
  let msr2 <- mkSeqRunning;
  let seqRunning2 = msr2.f;
  let mdsi <- mkDoSeqIntersectRes;
  let doSeqIntersectRes = mdsi.f;
  let s1 <- m1;
  let s2 <- m2;
  let run_1 <- mkReg(False);
  let run_2 <- mkReg(False);
  method running() ;   return (run_1 || run_2);
  endmethod: running
  method advance() ;
    actionvalue
      let {run_1a,res_l} <- !(run_1) && !(run_2) || run_1 ?
				(actionvalue
				   let r <- s1.advance;
				   return(tuple2(seqRunning1(r), r));
				 endactionvalue)
       :   actionvalue
	      return tuple2(False, SeqPending);
	   endactionvalue;
      let {run_2a,res_r} <- !(run_1) && !(run_2) || run_2 ?
				(actionvalue
				   let r2 <- s2.advance;
				   return(tuple2(seqRunning2(r2), r2));
				 endactionvalue)
       :   actionvalue
	      return tuple2(False, SeqPending);
	   endactionvalue;

      run_1 <= run_1a;
      run_2 <= run_2a;
      return(doSeqIntersectRes(res_l, res_r));
    endactionvalue
  endmethod: advance
endmodule: mkSeqIntersect

/*
(* noinline *)
function Tuple2#(Bool, SeqRes) doSeqFirstMatch(SeqRes r);
  return (begin case (r) matches
		tagged SeqFail :  (tuple2(False, SeqFail));
		tagged SeqPending :  (tuple2(True, SeqPending));
		tagged SeqHold :  (tuple2(False, SeqHoldStrong));
		tagged SeqHoldStrong :  (tuple2(False, SeqFail));
		endcase
	  end);
endfunction: doSeqFirstMatch
*/

(*always_ready*)
interface Wrap6;
   method Tuple2#(Bool, SeqRes) f(SeqRes r);
endinterface

(*synthesize*)
module mkDoSeqFirstMatch(Wrap6);
   method Tuple2#(Bool, SeqRes) f(SeqRes r);
      return (begin case (r) matches
		       tagged SeqFail :  (tuple2(False, SeqFail));
		       tagged SeqPending :  (tuple2(True, SeqPending));
		       tagged SeqHold :  (tuple2(False, SeqHoldStrong));
		       tagged SeqHoldStrong :  (tuple2(False, SeqFail)); // ??? JES
		    endcase
	      end);
   endmethod
endmodule

module mkSeqFirstMatch#(module#(Sequence) m)(Sequence);
  let mfm <- mkDoSeqFirstMatch;
  let doSeqFirstMatch = mfm.f;
  let s <- m;
  let run <- mkReg(False);
  method running() ;   return (run);
  endmethod: running
  method advance() ;
    actionvalue
       let r <- s.advance;
       match {.runa,.res} =
           doSeqFirstMatch(r);
       run <= runa; // JES
       return(res);
    endactionvalue
  endmethod: advance
endmodule: mkSeqFirstMatch

module mkSeqNull(Sequence);
  method running() ;   return False;
  endmethod: running
  method advance() ;   actionvalue return SeqHoldStrong; endactionvalue
  endmethod: advance
endmodule: mkSeqNull

/*
(* noinline *)
function Tuple3#(Bool, Maybe#(SeqRes), SeqRes) doSeqUnbound(SeqRes r, SeqRes f);
  return (begin case (r) matches
		tagged SeqFail :
		  ((f == SeqHold ?
			tuple3(False, Just (SeqPending), SeqHoldStrong)
		    :   tuple3(False, Just (SeqPending), SeqFail)));
		tagged SeqPending :  (tuple3(True, Nothing, SeqPending));
		tagged SeqHold :  (tuple3(True, Just (SeqHold), SeqHold));
		tagged SeqHoldStrong :  (tuple3(True, Just (SeqHold), SeqHold));
		endcase
	  end);
endfunction: doSeqUnbound
*/

(*always_ready*)
interface Wrap7;
   method Tuple3#(Bool, Maybe#(SeqRes), SeqRes) f(SeqRes r, SeqRes ff);
endinterface

(*synthesize*)
module mkDoSeqUnbound(Wrap7);
   method Tuple3#(Bool, Maybe#(SeqRes), SeqRes) f(SeqRes r, SeqRes ff);
      return (begin case (r) matches
		       tagged SeqFail :
			  ((ff == SeqHold ?
			    tuple3(False, Just (SeqPending), SeqHoldStrong)
			    :   tuple3(False, Just (SeqPending), SeqFail)));
		       tagged SeqPending :  (tuple3(True, Nothing, SeqPending));
		       tagged SeqHold :  (tuple3(True, Just (SeqHold), SeqHold));
		       tagged SeqHoldStrong :  (tuple3(True, Just (SeqHold), SeqHold));
		    endcase
	      end);
   endmethod
endmodule

module mkSeqUnbound#(module#(Sequence) m)(Sequence);
  let mdsu <- mkDoSeqUnbound;
  let doSeqUnbound = mdsu.f;
  let s <- m;
  let run <- mkReg(False);
  let res_ <- mkReg(SeqPending);
  method running() ;   return (False);
  endmethod: running
  method advance() ;
    actionvalue
      let r <- s.advance;
      match {.runa,.resa,.res} =
	  doSeqUnbound(r, res_);
      run <= runa;
      res_ <=
      begin case (resa) matches
	    tagged Nothing :  (res_);
	    tagged Just .n :  (n);
	    endcase
      end;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkSeqUnbound

module mkSeqRepConst#(module#(Sequence) m, Integer c)(Sequence);
   Sequence _ifc = ?;
   case (c)
      0: begin _ifc <- mkSeqNull(); end
      1: begin _ifc <- m; end
      default: if (c<0)
	 begin
	    let str = "SVA: the number of repetitions of a sequence (-";
	    str = strConcat(str, integerToString(-c));
	    str = strConcat(str, ") cannot be negative");
	    error(str);
	 end
	       else
	 begin
	    let m1 = mkSeqRepConst(m, c-1);
	    _ifc <- mkSeqConcat(m,m1);
	 end
   endcase
   method advance = _ifc.advance;
   method running = _ifc.running;
endmodule

module mkSeqRepRange#(module#(Sequence) m, Integer lo, Integer hi)(Sequence);
   Sequence _ifc = ?;
   if (lo>hi)
      begin
	 let str = "SVA: the lower bound (";
	 str = strConcat(str, integerToString(lo));
	 str = strConcat(str, ") of a sequence repetition range must not exceed the higher (");
	 str = strConcat(str, integerToString(hi));
	 str = strConcat(str, ")");
	 error(str);
      end
   else
      begin
	 let m0 = mkSeqRepConst(m,lo);
	 if (lo<hi)
	    begin
	       let m1 = mkSeqRepRange(m,lo+1,hi);
	       _ifc <- mkSeqOr(m0, m1);
	    end
	 else _ifc <- m0; // JES
      end
   method advance = _ifc.advance;
   method running = _ifc.running;
endmodule

(*synthesize*)
module mkDoSeqDelayUnbound(Wrap7);
   method Tuple3#(Bool, Maybe#(SeqRes), SeqRes) f(SeqRes r, SeqRes ff);
      return (begin case (r) matches
		       tagged SeqFail :
			  ((ff == SeqHold ?
			    tuple3(False, Just (SeqPending), SeqHoldStrong)
			    :   tuple3(False, Just (SeqPending), SeqFail)));
		       tagged SeqPending :  (tuple3(True, Nothing, SeqPending));
		       tagged SeqHold :  (tuple3(True, Just (SeqHold), SeqHold));
		       tagged SeqHoldStrong :  (tuple3(True, Just (SeqHold), SeqHold));
		    endcase
	      end);
   endmethod
endmodule

/*
module mkSeqDelayUnbound#(module#(Sequence) m)(Sequence);
  let mdsu <- mkDoSeqUnbound;
  let doSeqUnbound = mdsu.f;
  let s <- m;
  let run <- mkReg(False);
  let res_ <- mkReg(SeqPending);
  method running() ;   return (False);
  endmethod: running
  method advance() ;
    actionvalue
      let r <- s.advance;
      match {.runa,.resa,.res} =
	  doSeqUnbound(r, res_);
      run <= runa;
      res_ <=
      begin case (resa) matches
	    tagged Nothing :  (res_);
	    tagged Just .n :  (n);
	    endcase
      end;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkSeqDelayUnbound
*/

module mkSeqDelayConst#(module#(Sequence) m, Integer c)(Sequence);
   Sequence _ifc = ?;
   case (c)
      0: begin _ifc <- m; end
      default: if (c<0)
	 begin
	    let str = "SVA: a constant delay (-";
	    str = strConcat(str, integerToString(-c));
	    str = strConcat(str, ") cannot be negative");
	    error(str);
	 end
	       else
	 begin
	    let m1 = mkSeqRepConst(mkSeqNull, c);
	    _ifc <- mkSeqConcat(m1,m);
	 end
   endcase
   method advance = _ifc.advance;
   method running = _ifc.running;
endmodule


module mkSeqDelayRange#(module#(Sequence) m, Integer lo, Integer hi)(Sequence);
   Sequence _ifc = ?;
   if (lo>hi)
      begin
	 let str = "SVA: the lower bound (";
	 str = strConcat(str, integerToString(lo));
	 str = strConcat(str, ") of a delay range must not exceed the higher (");
	 str = strConcat(str, integerToString(hi));
	 str = strConcat(str, ")");
	 error(str);
      end
   else
      begin
	 let m0 = mkSeqDelayConst(m,lo);
	 if (lo<hi)
	    begin
	       let m1 = mkSeqDelayRange(m,lo+1,hi);
	       _ifc <- mkSeqOr(m0, m1);
	    end
	 else _ifc <- m0; // JES
      end
   method advance = _ifc.advance;
   method running = _ifc.running;
endmodule




// ======

// PROPERTIES

typedef enum {
  PropTrue, PropUndetermined, PropFalse, PropVacuous} PropRes deriving (Eq, Bits);

interface Property;
    method ActionValue#(PropRes) advance();
endinterface: Property

module mkPropSeq#(module#(Sequence) m)(Property);
  let s <- m;
  method advance() ;
    actionvalue
      let r <- s.advance;
      let res = case (r) matches
		 tagged SeqFail :  return(PropFalse);
		 tagged SeqPending :  return(PropUndetermined);
		 tagged SeqHold :  return(PropTrue);
		 tagged SeqHoldStrong :  return(PropTrue);
		 endcase;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkPropSeq

module mkPropNot#(Property prop)(Property);
  method advance() ;
    actionvalue
      let r <- prop.advance;
      let res = case (r) matches
		 tagged PropFalse :  return(PropTrue);
		 tagged PropUndetermined :  return(PropUndetermined);
		 tagged PropTrue :  return(PropFalse);
		 tagged PropVacuous :  return(PropFalse);
		 endcase;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkPropNot

module mkPropOr#(Property p1, Property p2)(Property);
  method advance() ;
    actionvalue
      let r1 <- p1.advance;
      let r2 <- p2.advance;
      let res = case (tuple2(r1, r2)) matches
		 {(tagged PropFalse),(tagged PropFalse)} :  return(PropFalse);
		 {(tagged PropTrue),.*} :  return(PropTrue);
		 {.*,(tagged PropTrue)} :  return(PropTrue);
		 {(tagged PropVacuous),.*} :  return(PropTrue);
		 {.*,(tagged PropVacuous)} :  return(PropTrue);
		 default :  return(PropUndetermined);
		 endcase;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkPropOr

module mkPropAnd#(Property p1, Property p2)(Property);
  method advance() ;
    actionvalue
      let r1 <- p1.advance;
      let r2 <- p2.advance;
      let res = case (tuple2(r1, r2)) matches
		 {(tagged PropTrue),(tagged PropTrue)} :  return(PropTrue);
		 {(tagged PropTrue),(tagged PropVacuous)} :  return(PropTrue);
		 {(tagged PropVacuous),(tagged PropTrue)} :  return(PropTrue);
		 {(tagged PropVacuous),(tagged PropVacuous)} :  return(PropTrue);
		 {(tagged PropFalse),.*} :  return(PropFalse);
		 {.*,(tagged PropFalse)} :  return(PropFalse);
		 default :  return(PropUndetermined);
		 endcase;
      return(res);
    endactionvalue
  endmethod: advance
endmodule: mkPropAnd

function Bool readReg(Reg#(Bool) r);
   return (r);
endfunction: readReg

// Turn: the first False element True, leaves others unchanged:
function List#(Bool) getFreeP (List#(Bool) x1);
   case (x1) matches
      tagged Nil:     return (Nil);
      tagged Cons {_1:.b, _2:.bs}:
	 return (!(b) ? Cons(True,bs) : Cons(b, getFreeP(bs)));
   endcase
endfunction: getFreeP

// Advances each non-free prop, returning list of Maybe results:
function ActionValue#(List#(Maybe#(PropRes))) runPs (List#(Property) x1, List#(Bool) x2);
   actionvalue
   case (tuple2(x1,x2)) matches
      {tagged Nil, .*}: return Nil;
      {.*, tagged Nil}: return Nil;

      {tagged Cons {_1:.p,_2:.ps}, tagged Cons {_1:.b,_2:.bs}}:
			actionvalue
			   let pres <- b ? (actionvalue
					       let pr <- p.advance;
					       return(Just (pr));
					    endactionvalue)
			   :   actionvalue return(Nothing); endactionvalue;
			   let rest <- runPs(ps, bs);
			   return Cons(pres, rest);
			endactionvalue
   endcase
   endactionvalue
endfunction: runPs

// Returns True if the result indicates the prop has just finished:
function Bool unRun (Maybe#(PropRes) x1);
   case (x1) matches
      tagged Just {tagged PropUndetermined}: return True;
      default: return False;
   endcase
endfunction: unRun

// Returns False if any element is False, otherwise True is any element is
// True or Vacuous, (otherwise Undetermined):
function PropRes getRes(List#(Maybe#(PropRes)) x1, PropRes x2);
   case (tuple2(x1,x2)) matches
      {tagged Nil, .res}: return (res);
      {tagged Cons {_1:tagged Just {tagged PropFalse},_2:.xs}, .res}:
				    return (PropFalse);
      {tagged Cons {_1:tagged Just {tagged PropTrue},_2:.xs}, .res}:
				    return getRes(xs, PropTrue);
      {tagged Cons {_1:tagged Just {tagged PropVacuous},_2:.xs}, .res}:
				    return getRes(xs, PropTrue);
      {tagged Cons {_1:.x,_2:.xs}, .res}: return getRes(xs, res);
   endcase
endfunction: getRes

function Action assignRegs (List#(Reg#(Bool)) x1, List#(Bool) x2);
   case (tuple2(x1,x2)) matches
      {tagged Nil, .*}: return noAction;
      {.*, tagged Nil}: return noAction;
      {tagged Cons {_1:.r,_2:.rs}, tagged Cons {_1:.b,_2:.bs}}:
				return (action
				   r <= b;
				   assignRegs(rs, bs);
				   endaction);
   endcase
endfunction: assignRegs

module mkPropImplies#(module#(Sequence) m, List#(Property) props)(Property);
   let s <- m;
   let rs <- replicateM(length(props), mkReg(False));
   method advance() ;
      actionvalue
	 let sr <- s.advance;
	 let bs = case (sr) matches
		     // If the sequence hasn't succeeded, get list of props in
		     // progress:
		     tagged SeqFail :  return(map(readReg, rs));
		     tagged SeqPending :  return(map(readReg, rs));
		     // If sequence has succeeded, add a free one (in order to
		     // start it off):
		     default :  return(getFreeP(map(readReg, rs)));
		  endcase;
	 // Advance all the props:
	 let pres <- runPs(props, bs);
	 // Clear the register of any which has just finished:
	 assignRegs(rs, map(unRun, pres));
	 // Return accumulated result (False trumping True):
	 return(getRes(pres, PropUndetermined));
      endactionvalue
   endmethod: advance
endmodule: mkPropImplies

typedef enum {
   AssertOkay, AssertFail} AssertRes deriving (Eq, Bits);

interface Assertion;
   method ActionValue#(AssertRes) advance();
endinterface: Assertion

module mkAssert#(Property prop, Action pass, Action fail)(Assertion);
   Reg#(Bool) going <- mkReg(True);
   method advance();
      actionvalue
	 if (going)
	    actionvalue
	       let r <- prop.advance;
	       let res <- case (r) matches
			     tagged PropFalse :
				(actionvalue
				 fail;
				 going <= False;
				 return(AssertFail);
				 endactionvalue);
			     tagged PropUndetermined :
				(actionvalue
				 return(AssertOkay);
				 endactionvalue);
			     tagged PropTrue :
				(actionvalue
				 pass;
				 going <= False;
				 return(AssertOkay);
				 endactionvalue);
			     tagged PropVacuous :
				(actionvalue
				 pass;
				 going <= False;
				 return(AssertOkay);
				 endactionvalue);
			  endcase;
	       return(res);
	    endactionvalue
	 else
	    actionvalue
	       return (AssertOkay);
	    endactionvalue
      endactionvalue
  endmethod: advance
endmodule: mkAssert

module mkAssertAlways#(List#(Property) props, Action pass, Action fail)(Assertion);
  let rs <- replicateM(length(props), mkReg(False));
  method advance() ;
    actionvalue
       let bs = getFreeP(map(readReg, rs));
       // Advance all the props:
       let pres <- runPs(props, bs);
       // Clear the register of any which has just finished:
       assignRegs(rs, map(unRun, pres));
       // Switch on accumulated result (False trumping True):
       case (getRes(pres, PropUndetermined)) matches
	  tagged PropFalse :
	     begin
		fail;
		return(AssertFail);
	     end
	  tagged PropUndetermined :
	     begin
		return(AssertOkay);
	     end
	  tagged PropTrue :
	     begin
		pass;
		return(AssertOkay);
	     end
	  tagged PropVacuous :
	     begin
		pass;
		return(AssertOkay);
	     end
       endcase
    endactionvalue
  endmethod: advance
endmodule: mkAssertAlways

/*
(*synthesize*)
module mkTest(Empty);
   let r <- mkReg(True);
   rule foo ($rose(r));
   endrule
endmodule
*/

endpackage: SVA
