import RegFile::*;
import Vector::*;

typedef enum {Init, Test}
  State deriving(Eq, Bits);

// Test a vector of regfiles to make sure that bug 1354 is fixed
// (an instance-name clash issue with multi-ported methods)

(* synthesize *)
module sysRegFileVector();

  Vector#(8, RegFile#(UInt#(3), UInt#(6))) rfs <- replicateM(mkRegFileFull);
  
  Reg#(State) state <- mkReg(Init);

  Reg#(UInt#(3)) idx <- mkReg(0);

  rule step;
    idx <= idx + 1;
  endrule

  rule do_init(state == Init);
    for(Integer i = 0; i < 8; i = i + 1) begin
       rfs[i].upd(idx, zeroExtend(idx)*fromInteger(i));
     end
  endrule

  (* descending_urgency = "end_init, step" *)
  rule end_init(state == Init && idx == 7);
     state <= Test;
     idx <= 0;
  endrule

  rule do_test(state == Test);
    Bool pass = True;
    for(Integer i = 0; i < 8; i = i + 1) begin
       pass = pass && rfs[i].sub(0) == fromInteger(i*0);
       pass = pass && rfs[i].sub(1) == fromInteger(i*1);
       pass = pass && rfs[i].sub(2) == fromInteger(i*2);
       pass = pass && rfs[i].sub(3) == fromInteger(i*3);
       pass = pass && rfs[i].sub(idx) == fromInteger(i)*zeroExtend(idx);
    end
    if(pass) 
      $display("Pass at idx %0d", idx);
    else
      $display("Fail at idx %0d", idx); 
    if(idx == 7) $finish(0);
  endrule

endmodule
  
          