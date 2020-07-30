import KbdV	::*;
import GetPut	::*;
import Paddle	::*;
import Ball	::*;

interface Controller;
    method Bool autoPlayL;
    method Bool autoPlayR;
endinterface: Controller

module mkController#(parameter Kbd kbd,
		     parameter Paddle paddleL,
		     parameter Paddle paddleR,
		     parameter Ball ball)(Controller);
  Reg#(UInt#(20)) repeatit();
  mkReg#(0) the_repeatit(repeatit);
  Reg#(Bool) autoL();
  mkReg#(True) the_autoL(autoL);
  Reg#(Bool) autoR();
  mkReg#(True) the_autoR(autoR);
  Reg#(Bool) doL();
  mkReg#(False) the_doL(doL);
  Reg#(Bool) upL();
  mkReg#(False) the_upL(upL);
  Reg#(Bool) doR();
  mkReg#(False) the_doR(doR);
  Reg#(Bool) upR();
  mkReg#(False) the_upR(upR);
  Reg#(Bool) releaseit();
  mkReg#(False) the_releaseit(releaseit);


  rule rule1Controller (True);
      ScanCode keycode;
      keycode <- kbd.get;
      case (keycode) matches
      tagged ScanCode ('hF0) :
	begin
	  releaseit<= True;
	end
      tagged ScanCode ('h1C) :
	begin
	  doL<= !releaseit; upL<= False; releaseit<= False;
	end
      tagged ScanCode ('h1A) :
	begin
	  doL<= !releaseit; upL<= True; releaseit<= False;
	end
      tagged ScanCode ('h15) :
	begin
	  autoL<= (releaseit ? autoL : !autoL); releaseit<= False;
	end
      tagged ScanCode ('h52) :
	begin
	  doR<= !releaseit; upR<= False; releaseit<= False;
	end
      tagged ScanCode ('h4A) :
	begin
	  doR<= !releaseit; upR<= True; releaseit<= False;
	end
      tagged ScanCode ('h5B) :
	begin
	  autoR<= (releaseit ? autoR : !autoR); releaseit<= False;
	end
      default :
	begin
	  releaseit<= False;
	end
      endcase
  endrule


  rule rule2Controller (True);
    repeatit <= (repeatit== 0 ? 110000 : repeatit- 1);
  endrule

  rule rule3Controller (repeatit== 0);
      if (doL)
        begin
	  paddleL.inc_dec(upL);
        end
      else if (autoL&& !ball.dir)
        begin
          paddleL.inc_dec(ball.center> paddleL.center);
        end
      else noAction;
      if (doR)
        begin
	  paddleR.inc_dec(upR);
        end
      else if (autoR&& ball.dir)
        begin
          paddleR.inc_dec(ball.center> paddleR.center);
        end
      else noAction;
  endrule

  method autoPlayL();
    return autoL;
  endmethod: autoPlayL
  method autoPlayR();
    return autoR;
  endmethod: autoPlayR

endmodule: mkController
