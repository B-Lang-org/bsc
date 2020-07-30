typedef enum { Square, Fourth, Eighth, Sixteenth, ThirtySecond, Data, Exit } TestState
  deriving(Eq, Bits);
 
(* synthesize *)
module sysBigBypassWire(Empty);

  Reg#(TestState) state <- mkReg(Square);

  Reg#(UInt#(8)) counter <- mkReg(0);
 
  Wire#(UInt#(512)) outputWire <- mkBypassWire;
  
  rule tick;
    counter <= counter + 1;
    state <= case (state) 
               Square: return(Fourth);
               Fourth: return(Eighth);
               Eighth: return(Sixteenth);
               Sixteenth: return(ThirtySecond);
               ThirtySecond: return(Data);
               Data:   return((counter == 23) ? Exit : Square);
             endcase;
  endrule

  UInt#(512) eCounter = zeroExtend(counter);
  let square = eCounter * eCounter;
  let fourth = square * square;
  let eighth = fourth * fourth;
  let sixteenth = eighth * eighth;
  let thirty_second = sixteenth * sixteenth;
  Bit#(64) phrase = 64'hdeadbeefbaadf00d;
  UInt#(512) data = unpack({phrase, phrase, phrase, phrase, 
                            phrase, phrase, phrase, phrase});
  rule drive_wire;
    outputWire <= case (state)
                    Square: return(square);
                    Fourth: return(fourth);
                    Eighth: return(eighth);
                    Sixteenth: return(sixteenth);
                    ThirtySecond: return(thirty_second);
                    default: return(data);
                  endcase;
  endrule
  
  rule display;
    $display("outputWire holds %h at time %t", outputWire, $time);
    if(state == Exit) $finish(0);
  endrule

endmodule
