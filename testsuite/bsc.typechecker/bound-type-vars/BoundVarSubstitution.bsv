import Vector::*;

interface Ifc#(numeric type numPixC,
               numeric type inPixWidth,
               numeric type outPixWidth);
    method Action newFrame();
endinterface

module mkTop1 ( Ifc#(numPixC,inPixWidth,outPixWidth) );
    SubIfc#(outPixWidth,outPixWidth) hscale <- mkSub1;
    Reg#(Vector#(numPixC,Bit#(outPixWidth))) inFIFO <- mkRegU;
endmodule

interface SubIfc#(numeric type inPixWidth,
                  numeric type outPixWidth);
    method Action newFrame;
endinterface

module mkSub1 ( SubIfc#(inPixWidth,outPixWidth) )
  provisos(
    Add#(c__, 8, TAdd#(1, TAdd#(inPixWidth, 8))),
    Add#(inPixWidth,c__,outPixWidth)
  );
endmodule

// ---------------

// Version which doesn't use TAdd
module mkSub2 ( SubIfc#(inPixWidth,outPixWidth) )
  provisos(
    Add#(inPixWidth, 8, ipw8),
    Add#(1, ipw8, ipw81),
    Add#(c__, 8, ipw81),
    Add#(inPixWidth,c__,outPixWidth)
  );
endmodule

// Copy of mkTop to instantiate it
module mkTop2 ( Ifc#(numPixC,inPixWidth,outPixWidth) );
    SubIfc#(outPixWidth,outPixWidth) hscale <- mkSub2;
    Reg#(Vector#(numPixC,Bit#(outPixWidth))) inFIFO <- mkRegU;
endmodule

