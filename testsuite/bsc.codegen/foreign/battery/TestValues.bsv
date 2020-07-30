import ValueImports::*;

(* synthesize *)
module mkTestValues ();
   Reg#(Bool) b <- mkReg(True);

   Bool s1 = string_compare("Hi","Mom!");
   Bool s2 = string_compare("Hi","Hi");

   rule disp (b);
      $display(" strcmp = %h", s1);
      $display(" strcmp = %h", s2);

      $display(" and32 = %h", and32(17,const_narrow));
      $display(" and32 = %h", and32('1,const_narrow));
      $display(" and32 = %h", and32('0,const_narrow));

      Bit#(128) v1 = {const_narrow, const_narrow, const_narrow, const_narrow};
      $display(" and128 = %h", and128(v1,const_wide));
      $display(" and128 = %h", and128(v1,zeroExtend(const_narrow)));
      $display(" and128 = %h", and128('1,const_wide));
      $display(" and128 = %h", and128('0,const_wide));

      Bit#(64) v2 = {const_narrow, const_narrow};
      $display(" andN = %h", andN(v2,v2));
      $display(" andN = %h", andN(v2,zeroExtend(const_narrow)));
      $display(" andN = %h", andN('1,v2));
      $display(" andN = %h", andN('0,v2));

      Bit#(96) v3 = {const_narrow, const_narrow, const_narrow};
      $display(" andN = %h", andN(v3,v3));
      $display(" andN = %h", andN(v3,zeroExtend(const_narrow)));
      $display(" andN = %h", andN('1,v3));
      $display(" andN = %h", andN('0,v3));

      // test system task values passed to foreign functions, and back

      // the value of $time is not going to the be same across tests,
      // so we use $test$plusargs below
      Bit#(64) t1 <- $time();
      Bit#(64) r1 = andN(t1,'0);
      $display (" andN($time,0) = %h", r1);

      Bit#(32) t2 <- $stime();
      Bit#(32) r2 = andN(t2,'0);
      $display (" andN($stime,0) = %h", r2);

      // use $test$plusargs
      Bool b1 <- $test$plusargs("Hi"); // True
      Bool b2 <- $test$plusargs("Hello"); // False
      $display(" b1 = %h", b1);
      $display(" b2 = %h", b2);
      // this also tests some logic on the result
      Bit#(32) bit1 = zeroExtend(pack(b1));
      Bit#(32) bit2 = zeroExtend(pack(b2));
      Bit#(32) bit3 = bit1 | (bit1 << 1);
      Bit#(32) bit4 = andN(bit3, 32'b11);
      Bit#(32) bit5 = andN(bit3, bit2 /* == '0 */);
      $display(" bit1 = %h", bit1);
      $display(" bit2 = %h", bit2);
      $display(" bit3 = %h", bit3);
      $display(" bit4 = %h", bit4);
      $display(" bit5 = %h", bit5);

      b <= False;
   endrule

   rule fin (!b);
      $finish(0);
   endrule

endmodule

	       
