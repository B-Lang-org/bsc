Integer five = message("five",5);

(* synthesize *)
module sysTestDefCache();
   
   Integer ten = five + five;
   
   rule test;
      $display(ten);
      $finish(0);
   endrule
   
endmodule
