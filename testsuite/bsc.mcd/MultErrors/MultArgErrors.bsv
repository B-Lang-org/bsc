(* synthesize *)
module mkParam#(parameter Bit#(32) p)(Reg#(Bit#(32)));

  Reg#(Bit#(32)) r <- mkReg(p);

  return(r);

endmodule

interface Counter;
  method Bit#(32) count;
  method Action reset(Bit#(32) value);
endinterface

(* synthesize *)
module mkCounter#(Bit#(32) inc)(Counter);

  Reg#(Bit#(32)) r <- mkReg(0);

  rule do_inc;
    r <= r + inc;
  endrule

  method count = r;
  method reset = r._write;

endmodule

(* synthesize *)
module mkMultArgErrors#(Clock c1, Clock c2, Reset r1, Reset r2)();

  Reg#(Bool) b <- mkRegU;

  Clock c = b ? c1 : c2;
  Reset r = b ? r1 : r2;

  Bit#(32) param = b ? 237 : 923;

  Bit#(32) arg_p = when(b, 255);

  Clock c_p = when(b, c1);
  Reset r_p = when(b, r2);
  Counter port_inst <- mkCounter(arg_p, clocked_by c_p, reset_by r_p);

  Reg#(Bit#(32)) param_inst <- mkParam(param, clocked_by c, reset_by r);
  Reg#(Bit#(32)) param_inst_2 <- mkParam(arg_p);
   
  rule test;
    $display(port_inst.count);
    $finish(0);
  endrule
       
endmodule
