typedef struct { Bit#(32) a; Bit#(16) b; } Bar;

function ActionValue#(Bit#(16)) getx();
  actionvalue
    $display("getx");
    return(0);
  endactionvalue
endfunction

function ActionValue#(Bit#(32)) gety();
  actionvalue 
    $display("gety");
    return(1);
  endactionvalue
endfunction

function ActionValue#(Bar) getBar();
  actionvalue
    Bar result;
    result.a <- gety;
    result.b <- getx;
    return(result);
  endactionvalue
endfunction
    
