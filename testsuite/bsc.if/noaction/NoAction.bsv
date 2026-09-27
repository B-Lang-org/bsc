// Each call is guarded so its p argument is true. The if (!p) actions
// therefore become noAction during expression transformation. Placing them
// before or after the live actions exercises elimination on both sides of
// joinActions. The live actions depend on another bit, so removing noAction
// must preserve both their conditions and their execution order.
function Action leftChain(Bool p, Integer n, Bit#(3) count);
   action
      if (n == 0)
         $display("left %0d", count);
      else begin
         if (!p) $display("FAIL left");
         if (count[1] == 1) $display("left step %0d %0d", count, n);
         leftChain(p, n - 1, count);
      end
   endaction
endfunction

function Action rightChain(Bool p, Integer n, Bit#(3) count);
   action
      if (n == 0)
         $display("right %0d", count);
      else begin
         rightChain(p, n - 1, count);
         if (count[1] == 1) $display("right step %0d %0d", count, n);
         if (!p) $display("FAIL right");
      end
   endaction
endfunction

(* synthesize *)
module sysNoAction(Empty);
   Reg#(Bit#(3)) count <- mkReg(0);
   Bool p = count[0] == 1;

   // Exercise both true-branch and false-branch assumptions about p.
   rule exercise;
      if (p) begin
         leftChain(p, 2, count);
         rightChain(p, 2, count);
      end
      else begin
         leftChain(!p, 2, count);
         rightChain(!p, 2, count);
      end
      count <= count + 1;
      if (count == 7) $finish(0);
   endrule
endmodule
