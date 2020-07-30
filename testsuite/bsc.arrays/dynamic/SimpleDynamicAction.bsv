(* synthesize *)
module sysSimpleDynamicAction(Empty);
   
   Action arr0[3] = {$display(0), $display(1), $display(2)};
   Action arr1[4] = {$display(3), $display(4), $display(5), $display(6)};
   
   Reg#(Bool) b <- mkReg(False);
   
   let arr = b ? arr0 : arr1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("arr[1]");
      arr[1];
      let arr2 = arr;
      arr2[2] = $display(7);
      $display("arr2[2]");
      arr2[2];
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
   endrule

endmodule
   
   
