import GetPut::*;
import RandGlobal::*;
import RandGen::*;

//(* synthesize *)
module mkRUser1(UserIfc);
  Reg#(Int#(8)) gap_counter();
  mkRegA#(0) the_gap_counter(gap_counter);
  Reg#(Nat) running_counter();
  mkRegA#(0) the_running_counter(running_counter);

//  GetCPut#(4,Bit#(6)) inFifo();
//  mkGetCPut the_inFifo(inFifo);
  GetPut#(Bit#(6)) inFifo();
  mkGetPut the_inFifo(inFifo);
  Get#(Bit#(6)) supply = inFifo.fst;

  Reg#(Bit#(6)) x();
  mkRegA#(0) the_x(x);

  Component2 cmp2;
  cmp2 =
   (interface Component2;
     method value;
      return x;
     endmethod
    endinterface);

  

  rule consume;
     running_counter <= running_counter + 1;
     gap_counter <= (gap_counter==0 ? 2 : gap_counter - 1);
     if (gap_counter == 0)
	action
	   Bit#(6) xx <- supply.get();
	   x <= xx;
	   $display("%d: 1 gets %h", running_counter, xx);
	endaction
  endrule
   
  return tuple2(inFifo.snd, cmp2);
endmodule

  
