interface Ifc;
   method ActionValue#(Bit#(8)) m();
endinterface

(* synthesize *)
module mkMethodActionValue_Sub (Ifc);
   method m = ?;
endmodule

(* synthesize *)
module sysMethodActionValue ();
  Ifc i <- mkMethodActionValue_Sub;

  rule r;
     let v <- i.m;
     $display(v + 8);
     $display(v - 1);
  endrule

endmodule

