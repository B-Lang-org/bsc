module pong(CLK,
	    hsync,
	    vsync,
	    red,
	    green,
	    blue,
	    kbclk,
	    kbdata,
	    sw1,
	    sw2,
	    display);
  input CLK;
  output hsync;
  output vsync;
  output [1 : 0] red;
  output [1 : 0] green;
  output [1 : 0] blue;
  output [6 : 0] display;
  input kbclk;
  input kbdata;
  input sw1;
  input sw2;

  wire RST_N;

  wire al, ar;

  wire CLOCK;
  assign CLOCK = CLK;

  mkTopLevel toplevel(
		.CLK(CLOCK),
		.RST_N(RST_N),
		.hsync(hsync),
		.vsync(vsync),
		.red(red),
		.green(green),
		.blue(blue),
		.rawkbd_kbclk_x1(kbclk),
		.rawkbd_kbdata_x1(kbdata),
		.rawsw1_iput_x1(sw1),
		.rawsw2_iput_x1(sw2),
		.aL(al),
		.aR(ar),
		.leds(display));

  wire expired;
  wire resetdone;
  wire rkbdata;

  reset rstgen(.clk(CLOCK), .kbdata(kbdata), .rstn(RST_N), .expired(expired), .resetdone(resetdone), .rkbdata(rkbdata));

  // assign display[0] = RST_N;
  // assign display[1] = expired;
  // assign display[2] = resetdone;
  // assign display[3] = rkbdata;
  // assign display[4] = sw1;
  // assign display[5] = al;
  // assign display[6] = ar;


endmodule
