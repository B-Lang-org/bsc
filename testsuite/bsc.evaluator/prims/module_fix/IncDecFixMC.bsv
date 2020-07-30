import ModuleCollect::*;
import List::*;

typedef ModuleCollect#(Integer, i) MyModule#(type i);

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
   
  addToCollection(5);
   
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
   
  addToCollection(7);
   
  method Action inc;
    s <= s + 1;
  endmethod

  method count = s;
endmodule

module [MyModule] mkAandB#(Tuple2#(Dec,Inc) ab)(Tuple2#(Dec,Inc));

  Dec a <- mkA(tpl_2(ab));
  Inc b <- mkB(tpl_1(ab));
   
  addToCollection(3);
 
  return(tuple2(a,b));

endmodule

module [MyModule] testIncDecFix();

  match {.a, .b} <- moduleFix(mkAandB);

  Reg#(UInt#(7)) count <- mkReg(0);

  rule run;
    if (count == 10) $finish(0);
    count <= count + 1;
    $display("a: %0d b: %0d count: %0d", a.count, b.count, count);
  endrule

endmodule

(* synthesize *)
module sysIncDecFixMC();
   
   let dut <- exposeCollection(testIncDecFix);
   
   mapM(messageM, map(integerToString, dut.collection));
   
endmodule

  
