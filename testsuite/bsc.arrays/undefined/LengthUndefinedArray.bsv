(* synthesize *)
module sysLengthUndefinedArray();

 int arr[4] = ?;

 rule test;
   $display(arrayLength(arr));
 endrule

endmodule
