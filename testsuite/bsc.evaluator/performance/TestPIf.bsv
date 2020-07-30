// Do: bsc -verilog -v -u Test.bsv
// 
// Compilation is very fast when using a Reg for q,
// but using a FIFO causes it to consume over 700MB of
// RAM and expanded takes over a minute.
//
// Using 2007.08.B, compilation is fast with the Reg,
// a little slow with the FIFO, but nowhere near as
// bad as the newer compilers.
//
//                  Reg         FIFO
// 2007.08.B   14s / 282MB   24s / 282MB
// r13160       9s / 276MB   92s / 718MB
   
import Vector::*;
import FIFO::*;

(* synthesize *)
module mkTestPIf();
   
  FIFO#(UInt#(8)) q <- mkFIFO();
//  Reg#(UInt#(8)) q <- mkReg(0);
  Reg#(Vector#(6,UInt#(9))) x <- mkRegU();

  rule accessHit;
    x <= fn(q.first(),q.first());
//    x <= fn(q,q);     
  endrule

endmodule

// This is generating a 256-element LUT
function UInt#(3) doLUT( UInt#(8) addr );
  Int#(9) sel = unpack({0,pack(addr)});
  if(sel == 255)
    sel = -1;

  UInt#(3) res = ?;
  for( Integer i = -1; i < 255; i = i+1 ) begin
    if( sel == fromInteger(i) )
      res = fromInteger( mod(i,6) );
  end   
  return res;
endfunction

function Vector#(6,UInt#(9)) fn( UInt#(8) x_in, UInt#(8) y_in);
  UInt#(3) x = doLUT(x_in);
  UInt#(3) y = doLUT(y_in);
  UInt#(6) x_plus_y = extend(x) + extend(y);

  // This is generating 5 53-element LUTs
  Vector#(6,UInt#(9)) v = ?;
  UInt#(3) idx = ?;
  for( Integer j=0; j < 5; j=j+1 ) begin
    for( Integer k=0; k < 53; k=k+1 ) begin
      if( x_plus_y + fromInteger(j) == fromInteger(k) ) begin
        idx = fromInteger( k % 6 );
      end
    end
    v[idx] = 100;    
  end
  return v;
endfunction
