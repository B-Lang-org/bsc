import VGACore::*;

Integer border;
border = 10;

Integer paddleDistFromWall;
paddleDistFromWall = 64;

Integer paddleWidth;
paddleWidth = 16;

Integer paddleHeight;
paddleHeight = 80;

Integer paddleEdgeDist;
paddleEdgeDist = 20 + border;

Integer ballWidth;
ballWidth = paddleWidth - 1;

Integer ballHeight;
ballHeight = div(ballWidth, 2) + 2;

Integer scoreLong;
scoreLong = 40;

Integer scoreShort;
scoreShort = 8;

typedef 3 NScoreDigits;

Integer scoreWallDist;
scoreWallDist = 100;

Integer scoreLx;
scoreLx = xMin + scoreWallDist;

Integer scoreRx;
scoreRx = xMax - (scoreWallDist + valueOf(NScoreDigits) * (scoreLong + scoreShort));

Integer scoreY;
scoreY = 30;

VGATiming vgaTiming;
vgaTiming = vga1280x480;

Integer hSize;
hSize = 1280;

Integer vSize;
vSize = 480;

Integer preScale;
preScale = 1;

Integer xMin;
xMin = 2 * border;

Integer xMax;
xMax = hSize - 2 * border;

Integer yMin;
yMin = border;

Integer yMax;
yMax = vSize - border;

typedef 12 XCoordSize;
typedef 11 YCoordSize;

typedef union tagged {
    Bit#(XCoordSize) XCoord;
} XCoord deriving (Literal, Eq, Ord, Arith, Bits, Bitwise);

typedef union tagged {
    Bit#(YCoordSize) YCoord;
} YCoord deriving (Literal, Eq, Ord, Arith, Bits, Bitwise);

typedef XCoord XSize;
typedef YCoord YSize;

function YCoord shiftY(YCoord y, Nat s);
  YCoord r;
  case (y) matches
    tagged YCoord .yc:
      r = YCoord (signedShiftRight(yc, s));
  endcase
  return r;
endfunction

function Bool posY(YCoord yc);
  Bool r;
  case (yc) matches
    tagged YCoord .x:
      r = x[fromInteger(valueOf(YCoordSize) - 1):fromInteger(valueOf(YCoordSize) - 1)] == 0;
  endcase
  return r;
endfunction

function Bool posX(XCoord xc);
  Bool r;
  case (xc) matches
    tagged XCoord .x:
      r = x[fromInteger(valueOf(XCoordSize) - 1):fromInteger(valueOf(XCoordSize) - 1)] == 0;
  endcase
  return r;
endfunction

function YCoord limitY(YCoord yc);
  Bit#(YCoordSize) limit = fromInteger(ballHeight - 4);
  YCoord r;
  case (yc) matches
    tagged YCoord .y:
      r = signedLT(y, negate(limit)) ? YCoord(negate(limit)) : 
          (signedLT(limit, y) ? YCoord(limit) : yc);
  endcase
  return r;
endfunction
