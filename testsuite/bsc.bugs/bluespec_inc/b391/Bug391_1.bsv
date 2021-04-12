interface Bug391_1_IFC;

  method Bit#(1) read ();
  method Bit#(1) write ();

endinterface: Bug391_1_IFC

(*
   synthesize,
   always_enabled,
   always_ready,
   CLK = "clk",
   RST_N = "reset"
*)

module mkBug391_1(Bug391_1_IFC);

  Reg#(Bit#(1)) read();
  mkRegA#(0) read(read);

  Reg#(Bit#(1)) write();
  mkRegA#(0) write(write);

  method read();
   read = write;
  endmethod: read

  method write();
   write = read;
  endmethod: write

endmodule: mkBug391_1
