import Vector :: *;
import EHR2 :: *;

interface RFile;
  method Action   wr( Rindx rindx, Bit#(32) data );
  method Bit#(32) rd1( Rindx rindx );
  method Bit#(32) rd2( Rindx rindx );
endinterface

typedef Bit#(5) Rindx;

(* synthesize *)
module mkRFile2( RFile );

  Vector#(32,EHR2#(Bit#(32))) rvec = newVector();

  for ( Integer x = 0; x < 32; x = x + 1 )
    rvec[x] <- mkEHR2;

  method Action wr( Rindx rindx, Bit#(32) data );
    (select(rvec,rindx)).r1 <= data;
  endmethod

  method Bit#(32) rd1( Rindx rindx );
    return ( rindx == 0 ) ? 0 : (select(rvec,rindx)).r2;
  endmethod

  method Bit#(32) rd2( Rindx rindx );
    return ( rindx == 0 ) ? 0 : (select(rvec,rindx)).r2;
  endmethod

endmodule


import StmtFSM :: *;

(* synthesize *)
module sysRFile2();
   let dut <- mkRFile2 ;
   
   Reg#(Bit#(32)) i <- mkReg(0);
   let tseq =
   seq
      for (i <= 0; i < 32; i <= i +1)
         seq
            action
               Bit#(5) idx = truncate(i);
               $display( "data at %d = %d %d", i, dut.rd1(idx), dut.rd2(idx) );
            endaction
            endseq
      for (i <= 0; i < 32; i <= i +1)
         seq
            action
               Bit#(5) idx = truncate(i);
               dut.wr( idx, (10000 + (100 *i ) + i ) );
            endaction
         endseq
      for (i <= 0; i < 32; i <= i +1)
         seq
            action
               Bit#(5) idx = truncate(i);
               $display( "data at %d = %d %d", i, dut.rd1(idx), dut.rd2(idx) );
            endaction
         endseq
   endseq;
   
   mkAutoFSM(tseq);
   
endmodule
