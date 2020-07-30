import GetPut::*;

typedef union tagged {
    Bit#(8) ScanCode;
} ScanCode deriving (Bits, Eq, Literal);

typedef Get#(ScanCode) Kbd;

interface RawKbd;
    method Action kbclk(Bool x1);
    method Action kbdata(Bool x1);
    method Bit#(8) key();
endinterface: RawKbd

module mkKbd(Tuple2#(RawKbd, Kbd));
     let mkVKbd1 = liftModule(mkVKbd);
   
     VKbd vkbd();
     mkVKbd1 thevkbd(vkbd);

     rule kbd_ack (vkbd.err == 1); 
       vkbd.ack;
     endrule

     return(tuple2(
            interface RawKbd;
	      method kbclk(x);
               action
                  if (x) vkbd.clk;
	       endaction
	      endmethod: kbclk
		      
       	      method kbdata(x); 
               action
                  if (x) vkbd.dta;
	       endaction
	      endmethod: kbdata

              method key(); 
                  return (vkbd.key);
	      endmethod: key
	    endinterface: RawKbd
           ,
	    interface Get;
	      method get() if (vkbd.rdy == 1 && vkbd.err == 0);
	       actionvalue
		vkbd.ack;
		return(ScanCode(vkbd.key));
	       endactionvalue
	      endmethod: get
	    endinterface: Get
           ));
endmodule: mkKbd

interface VKbd;
    method Bit#(8) key();
    method Bit#(1) rdy();
    method Bit#(1) err();
    method Action ack();
    method Action clk();
    method Action dta();
endinterface: VKbd

import "BVI" kbscan = module mkVKbd(VKbd);
  default_clock clk(clk);
  default_reset rstn(rstn);
  method (* reg *)o_byte     key;
  method (* reg *)o_byte_rdy rdy;
  method (* reg *)o_byte_err err;
  method ack() enable(i_byte_ack);
  method clk() enable((* reg *)i_kbclk);
  method dta() enable((* reg *)i_kbdata);

  schedule (key,rdy,err,ack,clk,dta) CF (key,rdy,err,ack,clk,dta);
     
     
endmodule: mkVKbd
