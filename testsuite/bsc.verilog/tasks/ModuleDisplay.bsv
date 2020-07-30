export sysModuleDisplay;

import GetPut::*;
import Connectable::*;

interface Stage#(type t);
  interface Put#(t) put_ifc;
  interface Get#(t) get_ifc;
endinterface

(* synthesize *)
module sysModuleDisplay(Empty);
  Reg#(UInt#(3)) count <- mkReg(0);

  Stage#(Int#(8)) stg1 <- mkPipeStage;
  Stage#(Int#(8)) stg2 <- mkPipeStage;
  Stage#(Int#(8)) stg3 <- mkPipeStage;
  Stage#(Int#(8)) stg4 <- mkPipeStage;

  Reg#(Bool) done <- mkReg(False);

  mkConnection(when(!done,stg1.get_ifc), stg2.put_ifc);
  mkConnection(when(!done,stg2.get_ifc), stg3.put_ifc);
  mkConnection(when(!done,stg3.get_ifc), stg4.put_ifc);

  rule in (!done);
    stg1.put_ifc.put(42); // put 42
  endrule: in

  rule out (!done);
    let unused <- stg4.get_ifc.get();  // get and discard
    count <= count + 1;
    if (count == 5)
      done <= True;
  endrule: out

  rule finish (done);
    $finish(0);
  endrule: finish

endmodule: sysModuleDisplay

(* synthesize *)
module mkPipeStage (Stage#(Int#(8)));

  Reg#(Maybe#(Int#(8))) val <- mkReg(Invalid);
  RWire#(Int#(8)) rw_p <- mkRWire;
  PulseWire pw_g <- mkPulseWire;

  rule do_put (rw_p.wget() matches tagged Valid .x);
      $displayo("%t %m: put val = %0d", $time, x);
      val <= Valid (x - 1);
  endrule: do_put

  rule do_get (pw_g);
      $display($time, " %m: get return = %0d", validValue(val));
      val <= Invalid;
  endrule: do_get

  interface Put put_ifc;
    method Action put(Int#(8) x) if (!isValid(val));
      rw_p.wset(x);
    endmethod
  endinterface: put_ifc

  interface Get get_ifc;
    method ActionValue#(Int#(8)) get() if (isValid(val));
      pw_g.send();
      return validValue(val);
    endmethod
  endinterface: get_ifc

endmodule: mkPipeStage