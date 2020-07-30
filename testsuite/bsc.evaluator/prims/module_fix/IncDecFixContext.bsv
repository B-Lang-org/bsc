import ModuleContext::*;
import List::*;

typedef ModuleContext#(Integer, i) MyModule#(type i);

module [MyModule] incInteger#(Integer i)();
  let j <- getContext;
  putContext (i + j);
endmodule

interface Inc;
  method Action inc();
  method Int#(32) count();
endinterface

interface Dec;
  method Action dec();
  method Int#(32) count();
endinterface

module [MyModule] mkA#(Inc b)(Dec);
  Reg#(Int#(32)) r <- mkReg(0);
   
  incInteger(1);
   
  rule do_inc(r == 0);
    r <= r + 1;
    b.inc;
  endrule

  method Action dec;
     r <= r - 1;
  endmethod

  method count = r;
endmodule

module [MyModule] mkB#(Dec a)(Inc);
  Reg#(Int#(32)) s <- mkReg(0);

  rule do_dec(s == 1);
    s <= s - 1;
    a.dec;
  endrule
   
  incInteger(2);
   
  method Action inc;
    s <= s + 1;
  endmethod

  method count = s;
endmodule

module [MyModule] mkAandB#(Tuple2#(Dec,Inc) ab)(Tuple2#(Dec,Inc));

  Dec a <- mkA(tpl_2(ab));
  Inc b <- mkB(tpl_1(ab));
   
  incInteger(3);
 
  return(tuple2(a,b));

endmodule

module [MyModule] testIncDecFix();

  match {.a, .b} <- moduleFix(mkAandB);

  Reg#(UInt#(7)) count <- mkReg(0);

  let i <- getContext;
  messageM(integerToString(i));

  rule run;
    if (count == 10) $finish(0);
    count <= count + 1;
    $display("a: %0d b: %0d count: %0d", a.count, b.count, count);
  endrule

endmodule

(* synthesize *)
module sysIncDecFixContext();
   
   runWithContext(0, testIncDecFix);
    
endmodule

  
