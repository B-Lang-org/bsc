import ConfigReg::*;

interface Switch;
    method Bool value();
endinterface: Switch

interface RawSwitch;
    method Action iput(Bool x1);
endinterface: RawSwitch

module mkSwitch (Tuple2 #(RawSwitch, Switch));
     Reg#(Bool) state();
     mkConfigRegU the_state(state);

     RawSwitch rawsw;
     rawsw = (interface RawSwitch;
                method iput(x);
                  action
                    state <= x;
                  endaction
                endmethod: iput
              endinterface);
     Switch sw;
     sw = (interface Switch;
             method value(); 
               return (!state);
             endmethod: value
           endinterface: Switch);
     return tuple2(rawsw,sw);
endmodule
