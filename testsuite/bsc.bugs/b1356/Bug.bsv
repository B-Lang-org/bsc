import BugFn::*;

(* noinline *)
function Bit#(32) some_function(Bit#(32) foo);
   begin
      return(foo - 3);
   end
endfunction

module mkBug(Empty);
   Reg#(Bit#(32)) count <- mkReg(0);

   rule countinc;
      count <= count + 1;
   endrule
endmodule
