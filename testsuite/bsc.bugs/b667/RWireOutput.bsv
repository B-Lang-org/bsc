interface Test;
  method Action in(Bit#(17) test);
  method Bit#(10) data();
  method Bit#(7) data2();
endinterface

(* synthesize *)
module sysRWireOutput(Test);

  RWire#(Bit#(17)) rw();
  mkRWire i_rw(rw);

  Reg#(Bool) b();
  mkReg#(False) i_b(b);
  
  Reg#(Bit#(17)) x();
  mkReg#(0) i_x(x);

  rule go;
      rw.wset(b ? (x*2) : (x*2 + 1));
  endrule

  method Action in(Bit#(17) test);
    action 
//      rw.wset(test);
    endaction
  endmethod

  method data();
    return(validValue(rw.wget())[9:0]);
  endmethod

  method data2();
    return(validValue(rw.wget())[16:10]);
  endmethod

endmodule

