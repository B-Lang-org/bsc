// test display of ActionValue

import GetPut::*;

module getProvider(Get#(Bit#(17)));

  Reg#(Bit#(17)) r();
  mkReg#(0) i_r(r);

  method get();
    actionvalue
      if(r == 0)   r <= 17;
      if(r == 17)  r <= 23;
      if(r == 23)  r <= 19;
      if(r == 19)  r <= 111;
      if(r == 111) r <= 37;
      if(r == 37)  r <= 3;
      if(r == 3) $finish(0);
      return(r);
    endactionvalue
  endmethod: get
endmodule: getProvider
           
module sysGetDisplay(Empty);

  Get#(Bit#(17)) get();
  getProvider i_get(get);
 
  rule go (True);
    $display("Get: %0d", get.get);
  endrule: go
endmodule: sysGetDisplay  
