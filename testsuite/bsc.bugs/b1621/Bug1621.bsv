(*noinline*)
function int summer (int a);
  for (int k = 20; k < 24; k = k+1)
     a = a + k;
  return a;
endfunction

(*noinline*)
function int summer2 (int a);
  for (int k = 20; k < 24; k = k+1)
     a = k + a;
  return a;
endfunction

(* synthesize *)
module sysBug1621();

   rule r;
      $display("x = %d", summer(10));
      $display("y = %d", summer2(20));
      $finish(0);
   endrule

endmodule
