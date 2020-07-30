(* synthesize *)
module sysDynamicActionDynamicIndex(Empty);
   
   Action arr0[3] = {$display(0), $display(1), $display(2)};
   Action arr1[4] = {$display(3), $display(4), $display(5), $display(6)};
   
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(2)) i <- mkReg(0);

   let arr = b ? arr0 : arr1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      arr[i];
      b <= !b;
      if (b) begin 
        i <= i + 1;
        if (i == 3) $finish(0);
      end 
   endrule

endmodule
   
   
