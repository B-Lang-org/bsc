
import "BDPI" function ActionValue#(Bit#(32)) my_time (Bit#(32) x);

typedef UInt#(51) NumTyp;

interface IFC #(type aTyp);
    method Action start(aTyp num1, aTyp num2);
    method aTyp result();
endinterface

(* synthesize *)
module mkGCDSub(IFC#(NumTyp));
    Reg#(NumTyp) x <- mkRegU;

    Reg#(NumTyp) y <- mkReg(0);

    rule flip (x > y && y != 0);
        x <= y;
        y <= x;
    endrule

    rule sub if (x <= y && y != 0);
        y <= y - x;
    endrule

    method Action start(NumTyp num1, NumTyp num2) if (y == 0);
        action
            x <= num1;
            y <= num2;
        endaction
    endmethod: start

    method NumTyp result() if (y == 0);
        result = x;
    endmethod: result
endmodule

(* synthesize *)
module sysGCD(Empty);
  IFC#(NumTyp) gcd <- mkGCDSub;

  Reg#(NumTyp) count1 <- mkReg(19);
  Reg#(NumTyp) count2 <- mkReg(5);
  
  Reg#(NumTyp) tbresult <- mkReg(0);

  rule rule1SendInput (True);
      gcd.start(count1, count2);
      count1 <= count1 + 3;
      count2 <= count2 + 2;
  endrule

  rule rule2GetResult (True);
      let res = gcd.result;
      tbresult <= res;
      $display("[%x] Received result: %h", my_time(0), res);
  endrule

  rule exit(count1 > 100);
    $finish(0);
  endrule

endmodule

