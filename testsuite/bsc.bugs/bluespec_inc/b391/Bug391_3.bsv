interface Bug391_3_IFC;

  method Bit#(1) read ();
  method Bit#(1) write ();

endinterface: Bug391_3_IFC

(*
   synthesize,
   always_enabled,
   always_ready,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBug391_3(Bug391_3_IFC);

  Reg#(Bit#(1)) read();
  mkRegA#(0) read_inst(read);

  Reg#(Bit#(1)) write();
  mkRegA#(0) write_inst(write);

  method read();
   read = write;
  endmethod: read

  method write();
   write = read;
  endmethod: write

endmodule: mkBug391_3
