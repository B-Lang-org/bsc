import GetPut::*;

interface SubIfc;
  interface Get#(int) reqGet;
endinterface

module mkSub (SubIfc);
  interface Get reqGet;
    method ActionValue#(int) get();
      return 0;
    endmethod
  endinterface
endmodule

