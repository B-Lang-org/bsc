import Global	::*;
import Counter2		::*;
import Shape	::*;
import Color::*;

XSize islandWidthC;
islandWidthC = fromInteger(islandWidth);

YSize islandHeightC;
islandHeightC = fromInteger(islandHeight);

YCoord islandLowC;
islandLowC = fromInteger(islandEdgeDist);

YCoord islandHighC;
islandHighC = fromInteger(vSize - islandHeight - islandEdgeDist);

YCoord islandStartC;
islandStartC = fromInteger(div((vSize- islandHeight), 2));

interface Island;
    method Shape shape;
    method YCoord center;
    method Action inc_dec(Bool x1);
    method Tuple5#(Bool, Bool, Bool, Bool, YSize) inside (XCoord x1, XCoord x2, YCoord x3, YCoord x4, YSize x5);
endinterface: Island

module mkIsland#(parameter Integer xpos)(Island);
  Counter#(YCoord) yposr();
  mkCounter#(islandLowC, islandStartC, islandHighC) the_yposr(yposr);
  Reg#(YCoord) centerR();
  mkRegU the_centerR(centerR);
  Shape islandRect();
  mkRectangle#(fromInteger(xpos),
	       islandWidthC,
	       yposr.get,
	       islandHeightC,
	       cRed) the_islandRect(islandRect);
  Reg#(YCoord) yposPlusHeight();
  mkRegU the_yposPlusHeight(yposPlusHeight);

  function Bool inside1(XCoord x, YCoord y);
  return (x > fromInteger(xpos) &&
	  x < fromInteger(xpos+ islandWidth) &&
	  y > yposr.get &&
	  y < yposPlusHeight);
  endfunction: inside1

  rule rule1Island (True);
    centerR <= yposr.get + (islandHeightC>> 1);
    yposPlusHeight <= yposr.get + islandHeightC;
  endrule

  method shape();
    return islandRect;
  endmethod: shape
  method center();
    return centerR;
  endmethod: center
  method inc_dec(up);
   action
    yposr.inc_dec(up);
   endaction
  endmethod: inc_dec

  method inside(x0, x1, y0, y1, dy);
    return tuple5( (inside1(x0, y0)),
                   (inside1(x0, y1)),
                   (inside1(x1, y0)),
                   (inside1(x1, y1)),
                   ((y0 - yposr.get) - ((islandHeightC- dy)>> 1))
                 );
  endmethod: inside

endmodule: mkIsland
