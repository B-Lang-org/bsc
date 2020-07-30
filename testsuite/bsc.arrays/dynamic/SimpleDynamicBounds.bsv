(* synthesize *)
module sysSimpleDynamicBounds(Empty);
   
   int arr0[3] = {0, 1, 2};
   int arr1[4] = {3, 4, 5, 6};
   
   Reg#(Bool) b <- mkReg(False);
   
   let arr = b ? arr0 : arr1;
   
   rule print;
      $display(arr[4]);
      $finish(0);
   endrule

endmodule
   
   
