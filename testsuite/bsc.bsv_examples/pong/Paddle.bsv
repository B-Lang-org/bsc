import Global   ::*;
import Counter2          ::*;
import Shape    ::*;
import Color::*;
              
XSize paddleWidthC;
paddleWidthC = fromInteger(paddleWidth);
                                        
YSize paddleHeightC;
paddleHeightC = fromInteger(paddleHeight);
                                          
YCoord paddleLowC;
paddleLowC = fromInteger(paddleEdgeDist);
                                         
YCoord paddleHighC;
paddleHighC = fromInteger(vSize - paddleHeight - paddleEdgeDist);
                                                                 
YCoord paddleStartC;
paddleStartC = fromInteger(div((vSize- paddleHeight), 2));
                                                          
interface Paddle;
    method Shape shape;
    method YCoord center;
    method Action inc_dec(Bool x1);
    method Tuple5#(Bool, Bool, Bool, Bool, YSize) insideit (XCoord x1, XCoord x2, YCoord x3, YCoord x4, YSize x5);
endinterface: Paddle
                    
module mkPaddle#(parameter Integer xpos)(Paddle);
  Counter#(YCoord) yposr();
  mkCounter#(paddleLowC, paddleStartC, paddleHighC) the_yposr(yposr);
  Reg#(YCoord) centerR();
  mkRegU the_centerR(centerR);
  Shape paddleRect();
  mkRectangle#(fromInteger(xpos),
               paddleWidthC,
               yposr.get,
               paddleHeightC,
               cRed) the_paddleRect(paddleRect);
  Reg#(YCoord) yposPlusHeight();
  mkRegU the_yposPlusHeight(yposPlusHeight);

  function Bool insideit1(XCoord x, YCoord y);
  return (x > fromInteger(xpos) &&
          x < fromInteger(xpos+ paddleWidth) &&
          y > yposr.get &&
          y < yposPlusHeight);
  endfunction: insideit1
  
  rule rule1Paddle (True); 
    centerR <= yposr.get + (paddleHeightC>> 1); 
    yposPlusHeight <= yposr.get + paddleHeightC;
  endrule

  method shape(); 
    return paddleRect;
  endmethod: shape
  method center(); 
    return centerR;
  endmethod: center
  method inc_dec(up);
   action 
    yposr.inc_dec(up);
   endaction
  endmethod: inc_dec

  method insideit(x0, x1, y0, y1, dy);
    return tuple5( (insideit1(x0, y0)), 
                   (insideit1(x0, y1)), 
                   (insideit1(x1, y0)), 
                   (insideit1(x1, y1)), 
                   ((y0 - yposr.get) - ((paddleHeightC- dy)>> 1))
                 );
  endmethod: insideit
  
endmodule: mkPaddle
                   


