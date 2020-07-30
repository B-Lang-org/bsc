import Global	::*;
import Counter2		::*;
import Shape	::*;
import Color::*;
	      
XSize islandWidthC;     islandWidthC = 100;
YSize islandHeightC;    islandHeightC = 60;

XCoord islandLeftC;     islandLeftC = 590;
YCoord islandLowC;      islandLowC = 210;
							  
interface Island;
    method Shape shape;
    method Tuple5#(Bool, Bool, Bool, Bool, YSize) insideit (XCoord x1, XCoord x2, YCoord x3, YCoord x4, YSize x5);
endinterface: Island
		    
module mkIsland(Island);
  Shape islandRect();
  mkRectangle#(islandLeftC,
	       islandWidthC,
	       islandLowC,
	       islandHeightC,
	       cRed) the_islandRect(islandRect);

  function Bool insideit1(XCoord x, YCoord y);
  return (x > islandLeftC &&
	  x < islandLeftC + islandWidthC &&
	  y > islandLowC &&
	  y < islandLowC + islandHeightC);
  endfunction: insideit1
  
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
  
endmodule: mkIsland
		   


