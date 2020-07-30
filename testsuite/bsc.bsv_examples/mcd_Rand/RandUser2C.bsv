import GetPut::*;
import CGetPut::*;
import RandGlobalC::*;
import RandGenC::*;

(* synthesize *)
module mkRUser2(UserIfc);
  Reg#(Int#(8)) counter();
  mkReg#(0) the_counter(counter);

  GetCPut#(4,Bit#(6)) inFifo();
  mkGetCPut the_inFifo(inFifo);
  Get#(Bit#(6)) supply = inFifo.fst;

  Reg#(Bit#(6)) x();
  mkReg#(0) the_x(x);

  Component2 cmp2;
  cmp2 =
   (interface Component2;
     method value;
      return x;
     endmethod
    endinterface);

  

  rule consume;
   action
     counter <= (counter==0 ? 30 : counter - 1);
     if (counter < 10)
      action
       Bit#(6) xx;
       xx <- supply.get();
       x <= xx;
       $display("2 gets %h", xx);
      endaction
   endaction
  endrule

  return tuple2(inFifo.snd, cmp2);
endmodule

  
