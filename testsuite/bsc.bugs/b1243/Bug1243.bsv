
// Bug 1243

// This example relies on some arbitrary decisions by the compiler.
// If it suddenly starts compiling, it may be due to the compiler
// picking different orderings; the example should be updated to
// trigger the bug with the new orderings.

// -----

// The submodule needs two methods which are CF but when calls to
// system tasks are taken into account, a path between them arises

// It also needs an intermediate method, which will (with proper
// biasing) lead to the two rules being in the proper order between
// the outer methods, without actually having a path

interface Ifc;
   method Action m1();
   method Action m2();
   method Action m3();
endinterface

(* synthesize *)
module mkBug1243_Sub (Ifc);

   Reg#(Bool) rg0 <- mkRegU;
   Reg#(Bool) rg1 <- mkRegU;
   Reg#(Bool) rg2 <- mkRegU;
   Reg#(Bool) rg3 <- mkRegU;

   // The use of $display in these two rules creates an order

   // This has to come after "m1" because of "rg1"
   // It also has to come before "m2" because of "rg3"
   rule r1;
      rg1 <= rg3;
      $display("Hello");
   endrule

   // This has to come before "m3" because of "rg2"
   // We hope that method-rule biasing will put this after "m2"
   rule r2;
      $display("World %h", rg2);
   endrule

   method Action m1();
      rg0 <= rg1;
   endmethod

   method Action m2();
      rg3 <= True;
   endmethod

   method Action m3();
      rg2 <= False;
   endmethod

endmodule

// -----

// The parent module needs two users that have an ordering
// which is different from the order chosen for the methods

(* synthesize *)
module sysBug1243 ();

   Ifc i <- mkBug1243_Sub;
   Reg#(Bool) rg0 <- mkRegU;
   Reg#(Bool) rg1 <- mkRegU;

   // This rule reads "rg1", so it comes before the other;
   // but calls "m3" which should come after "m1"
   rule r1;
      rg0 <= rg1;
      i.m3();
   endrule

   rule r2;
      rg1 <= True;
      i.m1();
   endrule

endmodule