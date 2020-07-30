// Test that the user cannot provide ports/expr for default clock "no_clock";

import "BVI" MOD =
module mkMyReg ( Clock aClk, 
		 Reg#(Bool) ifcout ) ;

   default_clock no_clock (CLK, (*unused*)CLK_GATE) = aClk ;
   no_reset ;
   
   method       _write(D_IN) enable(EN) clocked_by(no_clock);
   method Q_OUT _read                   clocked_by(no_clock);

   //schedule _read  CF  _read  ;
   //schedule _read  SB  _write ;
   //schedule _write SBR _write ;
endmodule

(* synthesize *)
module sysImportForeignModule_DeclareDefaultNoClock#(Clock a) (Empty);
   Reg#(Bool) rg <- mkMyReg(a);

   rule r;
      $display(rg);
   endrule
endmodule
