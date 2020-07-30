import "BDPI" MyAnd =
    function Bit#(8) my_and (Bit#(8) x, Bit#(8) y);

(* synthesize *)
module mkBDPI_CapitalLinkName ();
   rule r;
      $display("%d",my_and(1,2));
      $display("%d",my_and(3,2));
      $finish(0);
   endrule
endmodule

