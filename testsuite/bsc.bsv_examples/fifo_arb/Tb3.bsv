import Block3::*;
import Includes::*;

// very simple testbench riles
//  10 cycles of clocks of data in
//  50 cycles overall
function Rules mkTestRules( LabIFC blockIFC,  Reg#(DataT) count );
   return (
           rules  
              rule init (count == 0);    $dumpvars();        endrule
              rule cnt (True);           count <= count + 1; endrule
              rule finish (count >= 50); $finish(0);         endrule
              
              rule drive1 (count < 10);
                 DataT tmp = count + zeroExtend(32'h10000000) ;
                 blockIFC.push1( tmp );
                 $display("    Push1 %h", tmp);
              endrule
              
              rule drive2 (count < 10);
                 DataT tmp = count + zeroExtend(32'h20000000) ;
                 blockIFC.push2( tmp );
                 $display("    Push2 %h", tmp);
              endrule
              
              // back pressue if we don't pull data out
              //  where ever it is available
              // rule check (count[0] == 0);

              rule check (True);
                 // this will wait for something to come out
                 DataT res <- blockIFC.get();
                 $display("    Got            -> %h", res);
              endrule
           endrules
           );
endfunction


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
(* synthesize *)
module mkTb3 (Empty);
   LabIFC blockIFC();
   mkBlock3 iblock3(blockIFC);
   Reg #(DataT) count <- mkReg(0);
   addRules( mkTestRules( blockIFC, count ) );
endmodule
