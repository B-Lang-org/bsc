(* synthesize *)
module sysInstParam_DontCareDynSelect();
    Maybe#(Bit#(9)) initv = tagged Invalid;
    String s = " " + toHex(pack(initv));
    let m <- mkAltSourceProbe(s);
endmodule

import "BVI" AltSourceProbe =
    module mkAltSourceProbe#(String init_str) (Empty);
        parameter SOURCE_INITIAL_VALUE = init_str;
    endmodule

function Bit#(n) removeDontCares(Bit#(n) num);
    Bit#(n) res = 0;
    for(Integer i = 0; i < valueOf(n); i = i + 1)
        res[i] = (num[i] == 1'b1) ? 1'b1 : 1'b0;
    return res;
endfunction

function String toHex(Bit#(n) num)
provisos (
    Div#(n   , 4, ndig),
    Mul#(ndig, 4, nadj),
    Add#(pad , n, nadj)
);
    String dig[16] = {"0","1","2","3","4","5","6","7","8","9","a","b","c","d","e","f"};
    Bit#(nadj) numadj = extend(removeDontCares(num));
    String res = "";
    for(Integer i = valueOf(nadj) - 1; i >= 0; i = i - 4) begin
        Bit#(4) dign = numadj[i:i-3];
        res = res + dig[dign];
    end
    return res;
endfunction

