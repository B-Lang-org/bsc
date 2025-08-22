(* synthesize *)
module sysValuePlusargs ();
   Reg#(Bool) b <- mkReg(True);
   Reg#(Bit#(4)) result4     <- mkReg(1);
   Reg#(Bit#(8)) result8     <- mkReg(2);
   Reg#(Bit#(16)) result16   <- mkReg(3);
   Reg#(Bit#(20)) result20   <- mkReg(4);
   Reg#(Bit#(64)) result64   <- mkReg(5);
   Reg#(Bit#(128)) result128 <- mkReg(6);

   Reg#(Bit#(23)) resultNG  <- mkReg(7);
   Reg#(Bit#(64)) resultF   <- mkReg(8);
   Reg#(Bit#(256)) resultS <- mkReg(9);

   rule disp_rule (b);
      // binary
      let r4 <- $value$plusargs("r4=%b",result4);
      if(r4)
         $display("result4 = %h", result4);
      else
         $display("result4 is not given");
      // octal
      let r8 <- $value$plusargs("r8=%o",result8);
      if(r8)
         $display("result8 = %h", result8);
      else
         $display("result8 is not given");

      // decimal
      let r16 <- $value$plusargs("r16=%d",result16);
      if(r16)
         $display("result16 = %h", result16);
      else
         $display("result16 is not given");

      // hexadecimal
      let r20 <- $value$plusargs("r20=%h",result20);
      if(r20)
         $display("result20 = %h", result20);
      else
         $display("result20 is not given");

      // check 64 bit given as decimal
      let r64 <- $value$plusargs("r64=%d",result64);
      if(r64)
         $display("result64 = %d", result64);
      else
         $display("result64 is not given");

      // check 64 bit given as decimal
      let r128 <- $value$plusargs("r128=%d",result128);
      if(r128)
         $display("result128 = %0d", result128);//dislay has an issue with 128 bit without %0 it adds tabs!
      else
         $display("result128 is not given");

      // using 256 bit(32 chars) as string storage, as no other option I found
      let r256 <- $value$plusargs("r256=%s",resultS);
      if(r256)
         $display("resultS = %0s", resultS);
      else
         $display("resultS is not given");

      //check not given
      let rNG <- $value$plusargs("rNG=%b",resultNG);
      if(rNG)
         $display("resultNG = %h", resultNG);
      else
         $display("resultNG is not given");

      b <= False;
      $finish(0);
   endrule
endmodule
