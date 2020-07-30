(* synthesize *)
module mkD(Empty);
RWire#(Bit#(4)) r <- mkUnsafeRWire();

rule doR(True);
  r.wset(1);
  if (isJust(r.wget()))
    $display("%d",unJust(r.wget()));
endrule
   
endmodule
