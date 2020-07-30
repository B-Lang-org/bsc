import Global	::*;
import Counter2		::*;
import Shape	::*;
import Color::*;
import StmtFSM::*;
	      
typedef Bit#(2) CountType;
CountType maxCount;
maxCount = 1;

typedef Bit#(32) Double;
typedef Bit#(16) Single;
Single one; one = 'h3fff;

// The next function multiplies a double length integer (< 32768) by a single
// length number, giving the more significant half of the double-length
// result.  This is all more complicated than it ought to do, because the
// compiler primitives (for multiplication in particular) are not yet quite
// right.  We are working on this. 

function Single mult(Double x, Single y);
      return (truncate(signedShiftRight(x * (Double'(signExtend(y))),14)));
endfunction      

XSize islandWidthC;     islandWidthC = 100;
YSize islandHeightC;    islandHeightC = 60;

XCoord islandLeftC;     islandLeftC = 490;
XCoord islandRightC;    islandRightC = 690;
YCoord islandLowC;      islandLowC = 150;
YCoord islandHighC;     islandHighC = 270;

Single xCentre; xCentre = 590;
Single yCentre; yCentre = 210;

Double xRad; xRad = 400;
Double yRad; yRad = 150;
  
interface Island;
    method Shape shape;
    method Tuple5#(Bool, Bool, Bool, Bool, YSize) insideit (XCoord x1, XCoord x2, YCoord x3, YCoord x4, YSize x5);
    method Action tick;
endinterface: Island
		    
module mkIsland(Island);
  Reg#(XCoord) xpos();
  mkReg#(islandLeftC) the_xpos(xpos);

  Reg#(YCoord) ypos();
  mkReg#(islandLowC) the_ypos(ypos);

  Reg#(CountType) count();
  mkReg#(maxCount) the_count(count);

  Shape islandRect();
  mkRectangle#(xpos,
	       islandWidthC,
	       ypos,
	       islandHeightC,
	       cRed) the_islandRect(islandRect);

  function Bool insideit1(XCoord x, YCoord y);
  return (x > xpos &&
	  x < xpos + islandWidthC &&
	  y > ypos &&
	  y < ypos + islandHeightC);
  endfunction: insideit1
  
  Reg#(Single) cos(); mkReg#('h7fff) the_cos(cos); // cos(theta), initially 1.0
  Reg#(Single) sin(); mkReg#(0) the_sin(sin);      // sin(theta), initially 0

  Reg#(Single) ac();  mkRegU the_ac(ac);  // a.cos(theta)
  Reg#(Single) as();  mkRegU the_as(as);  // a.sin(theta)
  Reg#(Single) bc();  mkRegU the_bc(bc);  // b.cos(theta)
  Reg#(Single) bs();  mkRegU the_bs(bs);  // b.sin(theta)

  Double a = 3;   // delta = 1deg -- 2sinsq(delta/2)
  Double b = 286; //                  sin(delta)
  Single increments = 359;  // max-numbered increment for complete revolution  
                            // (starting at 0)

  Reg#(Single) incs();  mkReg#(0) the_incs(incs);

  Stmt positionStmt =
   seq
    action
     ac <= mult(a,cos);
     as <= mult(a,sin);
     bc <= mult(b,cos);
     bs <= mult(b,sin);
    endaction
    action
     cos  <= incs == 0 ? one : (cos - (ac + bs));
     sin  <= incs == 0 ? 0   : (sin - (as - bc));
     incs <= incs == 0 ? increments : (incs - 1);
    endaction
    action
     xpos <= unpack(truncate(pack(xCentre + mult(xRad, cos))));
     ypos <= unpack(truncate(pack(yCentre + mult(yRad, sin))));
    endaction
   endseq;

  FSM positionFSM();
  mkFSM#(positionStmt) the_position_FSM(positionFSM);

  Action updatePos = positionFSM.start;

  rule updatePosition (count == 0);
   action
     count <= maxCount;

     updatePos;
   endaction
  endrule

  method shape(); 
    return islandRect;
  endmethod: shape

  method insideit(x0, x1, y0, y1, dy);
    return tuple5( (insideit1(x0, y0)), 
                   (insideit1(x0, y1)), 
                   (insideit1(x1, y0)), 
                   (insideit1(x1, y1)), 
                   0  // this component not used
                 );
  endmethod: insideit
  
  method tick();
   action
    if (count != 0)
       count <= count - 1;
   endaction
  endmethod

endmodule: mkIsland
		   


