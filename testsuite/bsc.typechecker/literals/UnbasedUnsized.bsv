package UnbasedUnsized;

Bit#(8)  zeros8  = '0;
Bit#(8)  ones8   = '1;
Bit#(32) zeros32 = '0;
Bit#(32) ones32  = '1;

// Width inferred from function argument context
function Bool isAllZeros(Bit#(8) x);
    return (x == '0);
endfunction

function Bool isAllOnes(Bit#(8) x);
    return (x == '1);
endfunction

endpackage
