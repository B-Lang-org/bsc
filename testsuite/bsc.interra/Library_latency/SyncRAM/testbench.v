module testTopModule();

reg clk,reset;

mkDesign design_inst_bsc (
            .CLK(clk),
            .RST_N(reset));

initial
begin
  clk = 1'b0;
  reset = 1'b0;
  @(negedge clk);
  reset = 1'b1;
    
    `ifdef DUMP_WAVES
        $dumpfile("./design.dump");
        $dumpvars(0);
        $dumpon;
    `endif
end

always
  #5 clk = ~clk;


endmodule

