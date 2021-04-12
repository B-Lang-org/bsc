interface Bug391_2_IFC;

  method Bit#(1) read ();
  method Bit#(1) write ();

endinterface: Bug391_2_IFC

(*
   synthesize,
   always_enabled,
   always_ready,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBug391_2(Bug391_2_IFC);

  Reg#(Bit#(1)) read();
  mkRegA#(0) read(read);

  Reg#(Bit#(1)) write();
  mkRegA#(0) write(write);

endmodule: mkBug391_2
