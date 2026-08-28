// Identifiers that are reserved words in SystemVerilog (or std:: package
// class names) but legal BSV identifiers.  The generated Verilog must work
// with SystemVerilog-mode consumers (e.g. verilator with DPI): bsc emits
// these as escaped identifiers, warning G0131 for each.
(* synthesize *)
module sysSvKeywords();
   Reg#(Bit#(8)) process   <- mkReg(0);
   Reg#(Bit#(8)) semaphore <- mkReg(1);
   Reg#(Bit#(8)) mailbox   <- mkReg(2);
   Reg#(Bit#(8)) global    <- mkReg(3);
   Reg#(Bit#(8)) soft      <- mkReg(4);
   Reg#(Bit#(8)) strong    <- mkReg(5);
   Reg#(Bit#(8)) weak      <- mkReg(6);
   Reg#(Bit#(8)) uwire     <- mkReg(7);

   rule step;
      process   <= process + 1;
      semaphore <= semaphore + process;
      mailbox   <= mailbox + semaphore;
      global    <= global + mailbox;
      soft      <= soft + global;
      strong    <= strong + soft;
      weak      <= weak + strong;
      uwire     <= uwire + weak;
      if (process == 5) begin
         $display("values %0d %0d %0d %0d %0d %0d %0d %0d",
                  process, semaphore, mailbox, global, soft, strong, weak,
                  uwire);
         $finish(0);
      end
   endrule
endmodule
