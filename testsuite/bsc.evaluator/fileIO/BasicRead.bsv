String fname = "sysBasicRead.txt";

(* synthesize *)
module sysBasicRead ();
   Handle hdl <- openFile(fname, ReadMode);
   Bool done <- hIsEOF(hdl);
   while (!done) begin
      String str <- hGetLine(hdl);
      rule do_disp;
         $display("%s", str);
      endrule
      done <- hIsEOF(hdl);
   end
   hClose(hdl);
   mkSub;
endmodule

module mkSub ();
   Handle hdl <- openFile(fname, ReadMode);
   String str = "";
   Bool done <- hIsEOF(hdl);
   while (!done) begin
      Char c <- hGetChar(hdl);
      str = str + charToString(c);
      done <- hIsEOF(hdl);
   end
   rule do_disp;
      $display(str);
   endrule
   hClose(hdl);
endmodule

