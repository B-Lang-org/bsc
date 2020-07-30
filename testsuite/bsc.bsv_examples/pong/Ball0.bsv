import StmtFSM  ::*;
import Global   ::*;
import Paddle   ::*;
import Border   ::*;
import Shape    ::*;
import Color::*;
//import List::*;
import Vector::*;

typedef Tuple5#(Bool, Bool, Bool, Bool, YSize) PaddleInsideTyp;
              
interface Ball;
    method Shape shape;
    method YCoord center;
    method Bool dir;
    method Action tick;
endinterface: Ball
                  
Color col;
col = cYellow;
              
XSize ballWidthC;
ballWidthC = fromInteger(ballWidth);
                                    
YSize ballHeightC;
ballHeightC = fromInteger(ballHeight);

// bounce top   bottom up/down      => up/down
// bounce right left   right/left   => right/left
// The result is the new direction                                    

function Bool bounce (Bool x , Bool y , Bool z);
  Tuple3#(Bool,Bool,Bool) xyz;
  xyz = tuple3(x,y,z);
  case (xyz) matches
   {False , False , False } : return  False; // no hit
   {False , False , True  } : return  True;  // no hit
   {False , True  , False } : return  False; // dir same as perpendicular
   {False , True  , True  } : return  False; // dir opp to perpendicular
   {True  , False , False } : return  True;  // dir opp to perpendicular
   {True  , False , True  } : return  True;  // dir same as perpendicular
   {True  , True  , False } : return  False; // dir orthog to perpendicular
   {True  , True  , True  } : return  True;  // dir orthog to perpendicular
   default                     : return  False; // all cases specified, not needed
  endcase
endfunction: bounce
                                                                  
module mkBall#(Bit#(n) random,
               Paddle paddleL,
               Paddle paddleR,
               Action lAct,
               Action rAct)(Ball)
  provisos (Add#(x,2,n));
  
  Reg#(YCoord) centerR();
  mkRegU the_centerR(centerR);

  Reg#(XCoord) ball_x();
  mkReg#(fromInteger(div(hSize, 2))) the_ball_x(ball_x);

  Reg#(YCoord) ball_y();
  mkReg#(fromInteger(div(vSize, 2))) the_ball_y(ball_y);

  Reg#(XCoord) ball_x_r();
  mkRegU the_ball_x_r(ball_x_r);

  Reg#(YCoord) ball_y_b();
  mkRegU the_ball_y_b(ball_y_b);

  Reg#(XCoord) ball_vx();
  mkReg#(7) the_ball_vx(ball_vx);

  Reg#(YCoord) ball_vy();
  mkReg#(1) the_ball_vy(ball_vy);

  Shape ballRect();
  mkRectangle#(ball_x, ballWidthC, ball_y, ballHeightC, col) the_ballRect(ballRect);

  Reg#(YCoord) change_y();
  mkReg#(0) the_change_y(change_y);

  Reg#(Bool) ball_dx();
  mkRegU the_ball_dx(ball_dx);

  Reg#(Bool) ball_dy();
  mkRegU the_ball_dy(ball_dy);

  // break updating into several steps to meet timing

  // The following uses only one register, but more muxes and logic

  // Declaring a new name and making it a synonym for an existing
  // interface so no () needed for the following two lines
  Reg#(YCoord) ball_vy2;
  ball_vy2 =  asReg(ball_vy);
  Reg#(YCoord) ball_vy3;
  ball_vy3 =  asReg(ball_vy);

  // steps in updating the ball
  Stmt updateBallStmt =
   seq
      action
        ball_vx<= (posX(ball_vx)== ball_dx ? ball_vx : negate(ball_vx));
        ball_vy2<= (posY(ball_vy)== ball_dy ? ball_vy : negate(ball_vy));
      endaction
      action
        // random velocity change
        Bit#(2) r2;
        YCoord randV;
        // truncate is defined in both Prelude and UInt, must specify
        r2 = Prelude::truncate(random);
        case (r2)
          2'b00    :  randV = 1;
          2'b01    :  randV = -1;
          default  :  randV = 0;
        endcase
        ball_vy3 <= ball_vy2 + shiftY(change_y, 3) + ((change_y != 0) ? randV : 0);
      endaction
      action
        ball_vy<= limitY(ball_vy3);
      endaction
      action
        ball_x <= ball_x + ball_vx; ball_y <= ball_y + ball_vy;
      endaction
      action
        ball_x_r <= ball_x + ballWidthC; ball_y_b <= ball_y + ballHeightC;
      endaction
    endseq;

  FSM updateBallFSM();
  mkFSM#(updateBallStmt) the_FSM(updateBallFSM);

  Action updateBalls = updateBallFSM.start;

  Reg#(PaddleInsideTyp) lpd();
  mkRegU the_lpd(lpd);

  Reg#(PaddleInsideTyp) rpd();
  mkRegU the_rpd(rpd);

  Stmt tickActionStmt =
    seq
             action
               // Left Paddle
               lpd <= paddleL.insideit(ball_x, ball_x_r, ball_y, ball_y_b, ballHeightC);
               // Right Paddle
               rpd <= paddleR.insideit(ball_x, ball_x_r, ball_y, ball_y_b, ballHeightC);
             endaction
             action
               // New Direction for Y
                      //bounce (b00 || b10), 
                      //       (b01 || b11),
                      //       bounce (a00 || a10), 
                      //              (a01 || a11), ...
                      //              ()
               Bool diry;
               diry = bounce( (tpl_1(rpd) || tpl_3(rpd)), 
                              (tpl_2(rpd) || tpl_4(rpd)),
                      bounce( (tpl_1(lpd) || tpl_3(lpd)),
                              (tpl_2(lpd) || tpl_4(lpd)), 
                      ((ball_y <= (fromInteger(yMax- ballHeight))) &&       // down if too large
                                  ((ball_y < (fromInteger(yMin))) || (posY(ball_vy)))) 
                                                                            //  up  if too small 
                                    )
                            );

               // New direction for X
               // Need to know which wall for counting points
               // Need to know where on the paddle for changing vy
                      //bounce (a00 || a01), 
                      //       (a10 || a11),
                      //       bounce (b00 || b01), 
                      //              (b10 || b11), ...
                      //              ()
               
               Bool hitWallR;
               Bool hitWallL;
               hitWallR =  (ball_x > fromInteger(xMax- ballWidth));
               hitWallL =  (ball_x < fromInteger(xMin));

               Bool dirx;
               dirx = bounce( (tpl_1(rpd) || tpl_2(rpd)),
                              (tpl_3(rpd) || tpl_4(rpd)), 
                      bounce( (tpl_1(lpd) || tpl_2(lpd)), 
                              (tpl_3(lpd) || tpl_4(lpd)),
                                      ((!hitWallR) && (hitWallL || posX(ball_vx)))
                                    )
                            );

               change_y <= (((tpl_1(lpd) || tpl_2(lpd)) != (tpl_3(lpd) || tpl_4(lpd))) ? 
                            tpl_5(lpd) : 
                            (((tpl_1(rpd) || tpl_2(rpd)) != (tpl_3(rpd) || tpl_4(rpd))) ? 
                             tpl_5(rpd) :
                             0));
               
               if (hitWallR) 
                 rAct;
               else 
                 noAction;

               if (hitWallL)
                 lAct;
               else
                 noAction;
           
               ball_dx <= dirx;
               ball_dy <= diry;

               updateBalls;

             endaction
    endseq;
   
  FSM tickActionFSM();
  mkFSM#(tickActionStmt) the_tickAction_FSM(tickActionFSM);
   
  Action tickAction  = tickActionFSM.start;

  rule rule1Ball (True); 
    centerR <= ball_y + fromInteger(div(ballHeight, 2));
  endrule
    
  method shape(); 
    return ballRect;
  endmethod: shape
  method center(); 
    return centerR;
  endmethod: center
  method dir(); 
    return ball_dx;
  endmethod: dir
  method tick();
    action
      tickAction;
    endaction
  endmethod: tick
  
endmodule: mkBall
                 



