import List::*;
import Vector::*;
import FIFOF::*;
import ConfigReg::*;
     
(* synthesize *)
module [Module] mkBug851(Empty);
   
  Integer numBlocks = 8;
        
  List#(Reg#(Bool))   iblocks <- List::mapM(constFn(mkRegU), upto(0,7) );

  Reg#(Maybe#(Bit#(4))) x <- mkReg(Nothing);

  function Maybe#(Bit#(4)) getNum(Bit#(4) x, List#(Reg#(Bool)) li);
    case (decodeList(li)) matches
      tagged Invalid:
        return(Nothing);
      tagged Valid {.hd, .tl}:
        begin
          if (hd == False) 
            return (Just(x));
          else
            return(getNum(x + 1, tl));
        end
    endcase
  endfunction

  Maybe#(Bit#(4)) emptyBlock = getNum(0, iblocks);
   
  rule doThings(True);
    x <= emptyBlock;
  endrule

endmodule
