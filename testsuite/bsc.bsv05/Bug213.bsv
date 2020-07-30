module foo();
  Reg#(bit[7:0]) keycode();
  mkRegU inst_keycode(keycode);
  Reg#(Bool) r_release();
  mkRegU the_release(r_release);
  rule bar;
      // begin actual text in bug 213
      case (keycode)
      8'hF0 : 
         action
	  r_release<= True;
	 endaction
      // end actual text in bug 213
      endcase
  endrule
endmodule
