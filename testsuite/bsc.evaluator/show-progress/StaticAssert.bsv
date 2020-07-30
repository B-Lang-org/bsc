import List::*;
import Assert::*;

(* synthesize *)
module sysStaticAssert();

   List#(Integer) cs = cons(1, cons(2, cons(3, cons(4, nil))));

   for (Integer i = 0; i < length(cs); i = i + 1)
      begin 
        Integer c = cs[i];
        staticAssert(c > 0, "Too small");
      end

endmodule

