// Test that ports can be assigned monadically

module msgM #(String s, t v) (t);
   messageM(s);
   return v;
endmodule

import "BVI" MOD =
module mkMod #( Bit#(32) n )
              ( Empty ifcout ) ;

   String msg = strConcat("Instantiating mkMod with argument ",
			  bitToString(n));
   port (* reg *) IN <- msgM(msg, n);

endmodule

(* synthesize *)
module sysImportForeignModule_PortWithBind();
   mkMod(17);
endmodule
