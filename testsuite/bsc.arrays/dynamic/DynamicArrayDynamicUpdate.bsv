(* synthesize *)
module sysDynamicArrayDynamicUpdate(Empty);
   
   int arr0[3] = {0, 1, 2};
   int arr1[4] = {3, 4, 5, 6};
   
   Reg#(Bool) b <- mkReg(False);
   Reg#(Bit#(1)) i <- mkReg(0);
 
   let arr = b ? arr0 : arr1;
   let arr2 = arr;
   arr[i] = -1;

   rule print;
      
      if (b)
	 $display("b is True");
      else
	 $display("b is False");
      $display("arr[0]: %0d", arr[0]);
      $display("arr[1]: %0d", arr[1]);
      $display("arr[2]: %0d", arr[2]);
      if (!b) $display("arr[3]: %0d", arr[3]);
      if (arr == arr) 
        $display("Array is equal");
      else 
        $display ("Array is NOT equal");
      if (arr == arr2)
        $display("arr2 is EQUAL");
      else
        $display("arr2 is not equal");
      if (arr2 == arr1)
        $display("arr2 equals arr1");
      else
        $display("arr2 does not equal arr1");
   endrule
   
   rule toggle;      
      if (b) $finish(0);
      b <= !b;
      i <= i + 1;
   endrule

endmodule
   
   
