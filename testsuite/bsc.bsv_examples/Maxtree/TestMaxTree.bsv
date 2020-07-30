
package TestMaxTree;

import MaxTree::*;
import LFSR::*;
import Vector::*;

(* synthesize *)
// Top level
module sys_p2_fifo ( Empty );
   

   Ifc_MaxTree_Queues #(8)  dut();
   mkMaxTree8_p2_fifo i_dut(dut);

   Empty i1();
   sys_Maxtree8 #(dut) tester(i1);

endmodule // sys_


(* synthesize *)
// Top level 
module sys_2q ( Empty );
   
   Ifc_MaxTree_Queues #(8) dut();
   mkMaxTree8_2q i_dut (dut);

   Empty i1();
   sys_Maxtree8 #(dut) tester(i1);

endmodule // sys_

   
module sys_Maxtree8#( Ifc_MaxTree_Queues#(8) tree_ifc) ( Empty );
   
   // Make a counter testing
   Reg #(UInt#(32)) count() ;
   mkReg #(0) i_count(count) ;

   // Use LFSR to generate random data.
   LFSR #(Bit#(40)) rand40();
   mkFeedLFSR #(40'h80_00de_0007) i_rand1(rand40) ;
   
   // Rules
   rule init ( count <= 5 ) ;   
     count <= count + 1 ;
      if (count == 0) 
         $dumpvars() ;
   endrule
   
   rule run (count > 5);
     Bit#(64) t <- $time();
     $display("%t -- rule run", t ) ;  
     count <= count + 1 ;
     rand40.next ;

     Bit#(40) randv = rand40.value ;
     Vector#(8, BaseData) dlist = unpack(randv) ;
   
     $display("The input: %h", randv );
     for (Integer x = 0; x < 8; x = x+1 )
        $display("%d: %h", x, select( dlist, x ) ) ;
   
     $display("\n");

     tree_ifc.pushit( unpack(randv));
   endrule

   rule read (count > 5) ;
     let{ index, data } = tree_ifc.get()    ;
     tree_ifc.takeit ;
     Bit#(64) t <- $time();
     $display( "%t -- rule read-- %d, %h", t, index, data ) ;
   endrule
     
   rule endTest (count > 100 ); // rule to kill the simulation
     Bit#(64) t <- $time();
     $display("%t -- end test fired", t) ;
   
     $finish(0);
   endrule
        
endmodule



endpackage
  
