import List::*;
import Global::*;       
import Color::*;
	      
interface Shape;
    method Action newPos(XCoord x1, YCoord x2);
    method Color color;
endinterface: Shape
		   
Shape emptyShape;
emptyShape =
  (interface Shape;
     method newPos(x,y);
       return noAction;
     endmethod
     method color();
       return cNone;
     endmethod
   endinterface);
	 	      
function Shape joinShapes(Shape s1, Shape s2);
return (interface Shape;
          method newPos (x,y); 
            action
              s1.newPos(x, y); 
              s2.newPos(x, y);
            endaction
          endmethod
          method color();
            return ( colorOr (s1.color,s2.color) );
          endmethod
        endinterface);
endfunction: joinShapes
		       
function Action visCheck(Reg#(Bool) r, a lo, a v, a hi)
  provisos (Eq#(a));
  action
    r <= ((v != hi) && ((v == lo) || r));
  endaction
endfunction: visCheck
						   
module mkRectangle#(XCoord xl, XSize xs, YCoord yl, YSize ys, Color col)(Shape);
	    Reg#(Bool) xVis();
	    mkRegU the_xVis(xVis);
	    Reg#(Bool) yVis();
            mkRegU the_yVis(yVis);
            
            XCoord xh;
            YCoord yh;
            xh =  xl + xs;
            yh =  yl + ys;

            method newPos(x, y);
              action
                visCheck(xVis, xl, x, xh);
                visCheck(yVis, yl, y, yh);
              endaction
            endmethod: newPos
            method color(); 
              return (xVis && yVis ? col : cNone);
            endmethod: color
endmodule: mkRectangle
		
function Shape modShapeVis(function Color f(Color x1), Shape s);
  return (interface Shape;
	    method newPos(); 
              return (s.newPos);
	    endmethod: newPos
	    method color(); 
              return (f(s.color));
	    endmethod: color
	  endinterface: Shape);
endfunction: modShapeVis
			
function Shape joinManyShapes(List#(Shape) shapes);
  return (foldr(joinShapes, emptyShape, shapes));
endfunction: joinManyShapes
			   
