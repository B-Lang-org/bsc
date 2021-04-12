interface Bug391_4_SubIfc;
  method bit bar();
endinterface: Bug391_4_SubIfc

interface Bug391_4_IFC;
  interface Bug391_4_SubIfc foo;
endinterface: Bug391_4_IFC

(*
   synthesize,
   always_enabled,
   always_ready,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBug391_4(Bug391_4_IFC);

  Reg#(bit) foo_bar_ifc();
  mkRegA#(0) foo_bar(foo_bar_ifc);

  interface Bug391_4_SubIfc foo;
    method bit bar();
      return foo_bar_ifc;
    endmethod
  endinterface
endmodule: mkBug391_4
