import List::*;
import LFSR::*;
import VGACore::*;
import Global::*;
import LedDecoder::*;
import Controller::*;
import KbdV::*;
import Switch::*;
import Border::*;
import Paddle::*;
import Ball::*;
import Shape::*;
import Score::*;
import Color::*;
import Decimal::*; 

import ConfigReg::*;
import SVA::*;
import AssertionWires::*;

interface TopLevel;
    method Bit#(1) hsync();
    method Bit#(1) vsync();
    method Bit#(2) red();
    method Bit#(2) green();
    method Bit#(2) blue();
    interface RawKbd rawkbd;
    interface RawSwitch rawsw1;
    interface RawSwitch rawsw2;
    method Bit#(1) aL();
    method Bit#(1) aR();
    method Bit#(7) leds();
endinterface: TopLevel

interface TopLevelBSV;
    method Bit#(1) hsync();
    method Bit#(1) vsync();
    method Bit#(2) red();
    method Bit#(2) green();
    method Bit#(2) blue();
    interface RawKbd rawkbd;
    interface RawSwitch rawsw1;
    interface RawSwitch rawsw2;
    method Bit#(1) aL();
    method Bit#(1) aR();
endinterface: TopLevelBSV

Integer paddleLXMin;
paddleLXMin = xMin + paddleDistFromWall;

Integer paddleRXMin;
paddleRXMin = xMax - paddleDistFromWall - paddleWidth;

module [AssertModule] mkTopLevelBSV(TopLevelBSV);
  Tuple2 #(RawKbd, Kbd) rawKbd_kbd();
  mkKbd the_kbd(rawKbd_kbd);
  Kbd kbd = tpl_2(rawKbd_kbd);

  Tuple2 #(RawSwitch, Switch) rawSwitch_switch1();
  mkSwitch the_switch1(rawSwitch_switch1);
  Switch sw1 = tpl_2(rawSwitch_switch1);

  Tuple2 #(RawSwitch, Switch) rawSwitch_switch2();
  mkSwitch the_switch2(rawSwitch_switch2);
  Switch sw2 = tpl_2(rawSwitch_switch2);

  LFSR#(Bit#(32)) lfsr();
  mkLFSR_32 the_lfsr(lfsr);

  DecCounter#(NScoreDigits) scoreL();
  mkDecCounter#(0) the_scoreL(scoreL);

  DecCounter#(NScoreDigits) scoreR();
  mkDecCounter#(3) the_scoreR(scoreR);

  Shape dispL();
  mkScore#(scoreL, fromInteger(scoreRx), fromInteger(scoreY)) the_dispL(dispL);

  Shape dispR();
  mkScore#(scoreR, fromInteger(scoreLx), fromInteger(scoreY)) the_dispR(dispR);

  VGACore#(XCoord, YCoord) vgaCore();
  mkVGACore#(preScale, vgaTiming) the_vgaCore(vgaCore);

  Shape border();
  mkBorder the_border(border);

  Paddle paddleL();
  mkPaddle#(paddleLXMin) the_paddleL(paddleL);

  Paddle paddleR();
  mkPaddle#(paddleRXMin) the_paddleR(paddleR);

  Ball ball();
  mkBall#(lfsr.value, paddleL, paddleR, scoreL.inc, scoreR.inc) the_ball(ball);

  Controller controller();
  mkController#(kbd, paddleL, paddleR, ball) the_controller(controller);

  Reg#(Color) color();
  mkRegU the_color(color);

//flipCol col b =  modShapeVis(\ c -> b && c != cNone ? col <^> c : c);
  function Shape flipCol(Color col, Bool b, Shape s);
    function Color f(Color c);
      return  (b && c != cNone ? colorXOr(col, c) : c);  
    endfunction
    return modShapeVis(f,s);
  endfunction

//flipBCol col b =  modShapeVis(\ c -> b ? col <^> c : c);
  function Shape flipBCol(Color col, Bool b, Shape s);
    function Color f(Color c);
      return  (b ? colorXOr(col, c) : c);  
    endfunction
    return modShapeVis(f,s);
  endfunction

  List#(Shape) shapes = List::replicate(6, ?);

  shapes[0] = flipCol(makeRGB(2, 0, 1), sw1.value, border); // border'
  shapes[1] = flipCol(makeRGB(1, 1, 3), sw1.value, ball.shape); // ball'
  shapes[2] = flipCol(cYellow, controller.autoPlayL, paddleL.shape); // padL
  shapes[3] = flipCol(cYellow, controller.autoPlayR, paddleR.shape); // padR
  shapes[4] = dispL;
  shapes[5] = dispR;
  
  Shape pict =  joinManyShapes(shapes);
  Shape pictN =  flipBCol(cWhite, sw2.value, pict);
  function Color f (Color c);
    return (vgaCore.blank ? cNone : c);
  endfunction
  Shape pictBl =  modShapeVis(f, pictN);

  (* no_implicit_conditions, fire_when_enabled *)
  rule make_color
   (!(vgaCore.frameTick));
      (pict.newPos)(vgaCore.hPos, vgaCore.vPos);
      lfsr.next;
      color <= pictBl.color;
  endrule

  (* fire_when_enabled *)
  rule tick
   (vgaCore.frameTick); 
      ball.tick;
  endrule

  method hsync(); return (pack(vgaCore.not_hsync));
  endmethod: hsync

  method vsync(); return (pack(vgaCore.not_vsync));
  endmethod: vsync

  method red(); return (getRed(color));
  endmethod: red

  method green(); return (getGreen(color));
  endmethod: green

  method blue(); return (getBlue(color));
  endmethod: blue

  interface rawkbd =  tpl_1(rawKbd_kbd);

  interface rawsw1 = tpl_1(rawSwitch_switch1);

  interface rawsw2 = tpl_1(rawSwitch_switch2);

  method aL(); return (pack(controller.autoPlayL));
  endmethod: aL

  method aR(); return (pack(controller.autoPlayR));
  endmethod: aR

endmodule: mkTopLevelBSV

(* synthesize, always_ready, always_enabled *)
module [Module] mkTopLevel(TopLevel);
   Tuple2#(AssertionWires#(7), TopLevelBSV) awires_dut();
   exposeAssertionWires#(mkTopLevelBSV) the_dut(awires_dut);

   match {.awires, .dut} = awires_dut;

   Reg#(Bool) clearreg();
   mkConfigReg#(False) the_clearreg(clearreg);

   rule clear_wires (clearreg);
      awires.clear;
   endrule

   method hsync = dut.hsync;
   method vsync = dut.vsync;
   method red = dut.red;
   method green = dut.green;
   method blue = dut.blue;
   interface RawKbd rawkbd;
      method kbclk = dut.rawkbd.kbclk;
      method key = dut.rawkbd.key;
      method Action kbdata(x);
	 dut.rawkbd.kbdata(x);
	 clearreg <= !x;
      endmethod
   endinterface
   interface rawsw1 = dut.rawsw1;
   interface rawsw2 = dut.rawsw2;
   method aL = dut.aL;
   method aR = dut.aR;
   method leds = awires.wires;
endmodule



