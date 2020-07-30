(* synthesize *)
module sysSimpleDynamicTest(Empty);
   
   int arr0[3] = {0, 1, 2};
   int arr1[4] = {3, 4, 5, 6};
   
   Reg#(Bool) b <- mkReg(False);
   
   let arr = b ? arr0 : arr1;
   
   rule print;
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("arr[1]: %0d", arr[1]);
      if (arr == arr) 
        $display("Array is equal");
      else 
        $display ("Array is NOT equal");
      let arr2 = arr;
      arr2[2] = 7;
      $display("arr2[2]: %0d", arr2[2]);
      if(arr2 == arr)
        $display("arr2 is EQUAL");
      else
        $display("arr2 is not equal");
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
   endrule

endmodule
   
   
