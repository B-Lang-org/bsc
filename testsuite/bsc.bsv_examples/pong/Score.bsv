import Vector	::*;
import List	::*;
import Global	::*;
import Shape	::*;
import Color	::*;
import LedDecoder		::*;
import Decimal::*;
		
Integer long;
long = 40;
			       
Integer short;
short = 8;
				 
Integer longs;
longs =  long- short;

XSize longsx; longsx = fromInteger(longs);
YSize longsy; longsy = fromInteger(longs);
		     
module mkDigit#(parameter LedDigit digit, parameter XCoord x, parameter YCoord y)(Shape);
	  function m#(Shape) mkRectangle2 (XCoord x, Integer xw, YCoord y, Integer yw, Color c)
            provisos(IsModule#(m, c));
            return mkRectangle(x, fromInteger(xw), y>> 1, (fromInteger(yw))>> 1, c);
          endfunction

	  Shape seg6();
	  mkRectangle2#(x, long, y, short, cWhite) the_seg6(seg6);
	  Shape seg5();
	  mkRectangle2#(x, short, y, long, cWhite) the_seg5(seg5);
	  Shape seg4();
	  mkRectangle2#(x+ longsx, short, y, long, cWhite) the_seg4(seg4);
	  Shape seg3();
	  mkRectangle2#(x, long, y+ longsy, short, cWhite) the_seg3(seg3);
	  Shape seg2();
	  mkRectangle2#(x, short, y+ longsy, long, cWhite) the_seg2(seg2);
	  Shape seg1();
	  mkRectangle2#(x+ longsx, short, y+ longsy, long, cWhite) the_seg1(seg1);
	  Shape seg0();
	  mkRectangle2#(x, long, y + 2 * longsy, short, cWhite) the_seg0(seg0);
	  LedDecoder ldec();
	  mkLedDecoder the_ldec(ldec);
	  List#(Bool) mask;
	  mask = toList(unpack(ldec.decode(digit)));

          List#(Shape) segs = List::replicate(7, ?);
          segs[0] = seg0;
          segs[1] = seg1;
          segs[2] = seg2;
          segs[3] = seg3;
          segs[4] = seg4;
          segs[5] = seg5;
          segs[6] = seg6;

          function Shape maskShape(Bool vis, Shape s);
            function Color f(Color c);
              return (vis ? c : cNone);
            endfunction
            return modShapeVis(f , s);
	  endfunction
	  Shape disp =  joinManyShapes(List::zipWith(maskShape, mask, segs));
	  return(disp);
endmodule: mkDigit
		    
function m#(Shape) mkScore(DecCounter#(n) cnt, XCoord x, YCoord y) provisos(IsModule#(m, c));
return (mkDisplay(cnt.getDigits, x, y));
endfunction: mkScore
		    
module mkDisplay#(Vector#(n, Bit#(4)) digits, XCoord x, YCoord y)(Shape);
   Integer nv =  valueOf(n);
   Integer sep =  long+ short;
   XCoord right =  fromInteger((nv-1)* sep)+ x;

   function m#(Shape) f(Integer i) provisos (IsModule#(m, c));
      return mkDigit((toList(digits))[i], right - fromInteger(i * sep),
                     y);
   endfunction

   List#(Shape) glyphs = List::replicate(nv, ?);
   for (Integer j = 0; j<nv; j=j+1)
    begin
      Shape s <- f(j);
      glyphs[j] = s;
    end
   
   return(joinManyShapes(glyphs));
endmodule: mkDisplay
		      


