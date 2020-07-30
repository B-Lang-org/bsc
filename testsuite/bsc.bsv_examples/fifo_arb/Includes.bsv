// common data type input and output from arbiter FIFOs
typedef Bit#(32) DataT;

// define a single interface shared by the test blocks
interface LabIFC;
   method Action push1 (DataT a);
   method Action push2 (DataT a);
   method ActionValue#(DataT) get();
endinterface

// very simple testbench rules
//  10 cycles of data in
//  50 cycles overall
function Rules mkTestRules( LabIFC blockIFC,  Reg#(DataT) count );
   return (
           rules
              rule init (count == 0);    $dumpvars();        endrule
              rule cnt (True);           count <= count + 1; endrule
              rule finish (count >= 50); $finish(0);         endrule
              
              // data into FIFO1 starts with 1
              // implicit condition assures that this rule
              // only fires when the FIFO has space
              rule drive1 (count < 10);
                 DataT tmp = count + zeroExtend(32'h10000000) ;
                 blockIFC.push1( tmp );
                 $display("    Push1 %h", tmp);
              endrule
              
              // data into FIFO2 starts with 2
              // implicit condition assures that this rule
              // only fires when the FIFO has space
              rule drive2 (count < 10);
                 DataT tmp = count + zeroExtend(32'h20000000) ;
                 blockIFC.push2( tmp );
                 $display("    Push2 %h", tmp);
              endrule

              // implicit condition assures that this rule 
              // will fire only when data is available
              rule check (True);
                 DataT res <- blockIFC.get();
                 $display("    Got            -> %h", res);
              endrule
           endrules
           );
endfunction
// test rules
