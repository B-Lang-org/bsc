interface ThreeClocks;
   interface Clock a;
   interface Clock b;
   interface Clock c;
endinterface

import "BVI" ThreeClocks =
module mk3Clocks1(ThreeClocks);
   default_clock no_clock;
   default_reset no_reset;
   output_clock a(CLK_a);
   output_clock b(CLK_b);
   output_clock c(CLK_c);
   
   ancestor(a,b);
   ancestor(b,c);
endmodule
      
import "BVI" ThreeClocks =
module mk3Clocks2(ThreeClocks);
   default_clock no_clock;
   default_reset no_reset;
   output_clock a(CLK_a);
   output_clock b(CLK_b);
   output_clock c(CLK_c);
   
   ancestor(a,c);
   ancestor(b,c);
endmodule

(* synthesize *)
module sysTransitiveAncestor();
   
   ThreeClocks one <- mk3Clocks1;
   ThreeClocks two <- mk3Clocks2;
   
   rule test;
      if(isAncestor(one.c, one.a))
	 $display("one pass");
      else
	 $display("one fail");
      
      if(sameFamily(two.a, two.b) && !isAncestor(two.a, two.b))
	 $display("two pass");
      else
	 $display("two fail");
      
      $finish(0);
   endrule
   
endmodule
