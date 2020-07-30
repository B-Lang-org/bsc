interface Bug391_5_SubIfc;
  method bit bar();
endinterface: Bug391_5_SubIfc

interface Bug391_5_IFC;
  interface Bug391_5_SubIfc foo;
endinterface: Bug391_5_IFC

(*
   synthesize,
   always_enabled,
   always_ready,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBug391_5(Bug391_5_IFC);
  Reg#(bit) foo_bar_ifc();
  mkRegA#(0) foo_bar(foo_bar_ifc);
endmodule: mkBug391_5
