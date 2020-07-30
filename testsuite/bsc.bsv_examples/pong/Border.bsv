import Global	::*;
import Shape	::*;
import Color::*;
	      
Color col;
col = cBlue;
	    
module mkBorder(Shape);
	     Shape rect();
	     mkRectangle#(fromInteger(xMin),
                          fromInteger(xMax - xMin),
                          fromInteger(yMin),
                          fromInteger(yMax - yMin),
                          col) the_rect(rect);
	     return(modShapeVis(colorXOr(col), rect));
endmodule

