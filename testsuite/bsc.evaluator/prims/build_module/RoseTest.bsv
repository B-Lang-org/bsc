module modRose#(a v)(Bool) provisos(Bits#(a, sa), Ord#(a));
   Reg#(a) oldVal <- mkRegU;

   rule update;
      oldVal <= v;
   endrule

   return(oldVal < v);
endmodule

function Bool rose(a v) provisos(Bits#(a, sa), Ord#(a));
   let c = clockOf(v);
   let r = resetOf(v);
   return(primBuildModule(primGetName(foo),c,r,modRose(v)));
endfunction

(* synthesize *)
module sysRoseTest();

   Reg#(Int#(4)) testReg <- mkReg(0);

   rule count;
      testReg <= testReg + 1;
   endrule

   rule test;
      $display("Test reg: %0d", testReg);
      if(testReg != 0)
	 if(rose(testReg))
	    $display("Test reg rose");
	 else
	    $display("Test reg fell");
   endrule

   rule exit(testReg == -1);
      $finish(0);
   endrule

endmodule
