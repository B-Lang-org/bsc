package Registers;

import Vector :: *;

interface MYRegFile;
  method Bit#(12) sub1(Bit#(6) addr);
  method Bit#(12) sub2(Bit#(6) addr);
  method Action upd(Bit#(6) addr,Bit#(12) dat);
  method Action clear(Bit#(1) cl);
endinterface: MYRegFile

(* synthesize *)
module mkRS (MYRegFile);
    Vector #(64, Reg #(Bit #(12))) rs <- replicateM (mkReg (0));

    RWire#(Bit#(1)) clear_reg <- mkRWire;

    rule clear_mem (clear_reg.wget == Just(1));
	  for (Integer i=0;i<64;i=i+1)
	    begin
          (select(rs,i)) <= 0;
		end
	endrule

    method sub1 (addr);
        return (select(rs,addr)._read);            
    endmethod

    method sub2 (addr);
        return (select(rs,addr)._read);            
    endmethod

    method Action upd (addr, dat);
       begin
        (select(rs,addr)) <= dat;
       end
    endmethod
    
    method Action clear (cl);
	  clear_reg.wset(cl);
    endmethod

endmodule

endpackage
