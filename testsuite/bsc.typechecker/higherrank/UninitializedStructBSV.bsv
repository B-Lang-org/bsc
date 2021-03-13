import UninitializedStruct::*;

(* synthesize *)
module sysUninitializedStructBSV();
   Foo f;
   f.x.fst = ?;
   f.x.snd = 42;

   rule doDisplay(True);
       $display(fshow(f.x.fst));
       $display(fshow(f.x.snd));
       $finish(0);
   endrule

endmodule
