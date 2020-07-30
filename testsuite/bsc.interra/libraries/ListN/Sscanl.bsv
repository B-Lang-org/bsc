package Sscanl;

import ListN :: *;

function Action displayabc (a abc) provisos (Bits #(a, sa));
    action
      $display ("%d", abc);
    endaction
endfunction



function Action display_list (ListN #(n,a) my_list) provisos (Bits # (a,sa));
     action
       joinActions ( map (displayabc, my_list));
     endaction
endfunction

function Bit #(16) my_mult (Bit #(16) b, Bit #(8) a);
   return (zeroExtend (a) * b);
endfunction


module mkTestbench_Sscanl();
   ListN #(7,Bit #(8)) my_list1 = cons (1, cons (2, cons (3, cons (4, cons (5, cons (6, cons (7, nil)))))));
   ListN #(7,Bit #(16)) my_list2 = cons (1, cons (2, cons (6, cons (24, cons (120, cons (720, cons (5040, nil)))))));

   ListN #(7,Bit #(16)) my_list3 = sscanl (my_mult, 16'd1, my_list1);

   rule fire_once (True);
      $display("Original ListN:");
      display_list(my_list1);
      $display("Scanned ListN (Factorial):");
      display_list(my_list3);
      if (my_list2 != my_list3) 
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_Sscanl
endpackage : Sscanl
