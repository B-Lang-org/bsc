package MethodUrg;

interface Test_ifc ;
   method Action highx(Int#(32) din );
   method Action lowx(Int#(32) din );
endinterface

(* synthesize *)
module mkTestUrg( Test_ifc );

   Reg#(Int#(32)) holder() ;
   mkRegU  i_holder(holder);

   method lowx( din ); action
      holder <= din ;
   endaction endmethod

   method highx( din ); action      
      holder <= din ;
   endaction endmethod
   

endmodule


endpackage
