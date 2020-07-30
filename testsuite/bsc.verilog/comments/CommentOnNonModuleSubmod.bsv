import ModuleCollect::*;
import List::*;

typedef ModuleCollect#(Bool, i) BoolModule#(type i);

module [BoolModule] mkBoolReg(Reg#(Bool));
   Reg#(Bool) r <- mkReg(False);
   addToCollection(r);
   return r;
endmodule

                     
module [Module] exposeBool#(BoolModule#(i) mkI)(Tuple2#(Bool,i));
   IWithCollection#(Bool, i) ecs();
   exposeCollection#(mkI) the_dut(ecs);

   function Bool isTrue(Bool x); return x; endfunction

   let dut = ecs.device;
   let res = any(isTrue, ecs.collection);

   return(tuple2(res,dut));
endmodule

        
module [BoolModule] mkTest(Empty);
  Reg#(Bool) a();
  mkBoolReg i_a(a);

  (* doc = "This is a BoolReg" *)
  Reg#(Bool) b();
  mkBoolReg i_b(b);

  rule do_flip;
    a <= b;
    b <= a;
  endrule
endmodule

(* synthesize *)
module [Module] mkCommentOnNonModuleSubmod(Reg#(Bool));
  (* doc = "This is the test" *)
  Tuple2#(Bool, Empty) test();
  exposeBool#(mkTest) i_test(test);

  method _read = tpl_1(test);
  method _write = constFn(noAction);
endmodule

