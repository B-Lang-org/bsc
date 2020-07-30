import Printf::*;

(* synthesize *)
module sysPrintfTest();

   Reg#(Bool) done <- mkReg(False);

   rule do_disp( !done );

    $display("#---- No format");
    begin
      String s = sprintf("Hello World!");
      $display("%s", s);
    end

    $display("#---- %%%%");
    begin
      String s = sprintf("%% %% %%");
      $display("%s", s);
    end

    $display("#---- %%c %%C");
    begin
      Char c1 = "x";
      Char c2 = "W";
      Char c3 = "*";
      String s = sprintf("%c %c %c, %C %C %C", c1, c2, c3, c1, c2, c3);
      $display("%s", s);
    end

    $display("#---- %%s %%S");
    begin
      String s1 = "Hello World!";
      String s2 = "";
      String s = sprintf("'%s' '%s', '%S' '%S'", s1, s2, s1, s2);
      $display("%s", s);
    end

    Integer i1 = 8;
    Integer i2 = 1234567890;
    Integer i3 = 0;
    Integer i4 = -17;

    Bit#(32) b1 = fromInteger(i1);
    Bit#(32) b2 = fromInteger(i2);
    Bit#(32) b3 = fromInteger(i3);

    UInt#(32) ub1 = fromInteger(i1);
    UInt#(32) ub2 = fromInteger(i2);
    UInt#(32) ub3 = fromInteger(i3);

    Int#(32) ib1 = fromInteger(i1);
    Int#(32) ib2 = fromInteger(i2);
    Int#(32) ib3 = fromInteger(i3);
    Int#(32) ib4 = fromInteger(i4);

    $display("#---- %%d");
    begin
      String s = sprintf("Integer '%d' '%d' '%d' '%d'", i1, i2, i3, i4);
      $display("%s", s);

      s = sprintf("Bit     '%d' '%d' '%d'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%d' '%d' '%d'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%d' '%d' '%d' '%d'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%D");
    begin
      String s = sprintf("'%D' '%D' '%D' '%D'", i1, i2, i3, i4);
      $display("%s", s);
    end

    $display("#---- %%i");
    begin
      String s = sprintf("'%i' '%i' '%i' '%i'", i1, i2, i3, i4);
      $display("%s", s);
    end

    $display("#---- %%I");
    begin
      String s = sprintf("'%I' '%I' '%I' '%I'", i1, i2, i3, i4);
      $display("%s", s);
    end

    $display("#---- %%+d");
    begin
      String s = sprintf("'%+d' '%+d' '%+d' '%+d'", i1, i2, i3, i4);
      $display("%s", s);
    end

    $display("#---- %%-8d");
    begin
      String s = sprintf("Integer '%-8d' '%-8d' '%-8d' '%-8d'", i1, i2, i3, i4);
      $display("%s", s);

      s = sprintf("Bit     '%-8d' '%-8d' '%-8d'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%-8d' '%-8d' '%-8d'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%-8d' '%-8d' '%-8d' '%-8d'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%4d");
    begin
      String s = sprintf("Integer '%4d' '%4d' '%4d' '%4d'", i1, i2, i3, i4);
      $display("%s", s);

      s = sprintf("Bit     '%4d' '%4d' '%4d'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%4d' '%4d' '%4d'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%4d' '%4d' '%4d' '%4d'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%.4d");
    begin
      String s = sprintf("Integer '%.4d' '%.4d' '%.4d' '%.4d'", i1, i2, i3, i4);
      $display("%s", s);

      s = sprintf("Bit     '%.4d' '%.4d' '%.4d'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%.4d' '%.4d' '%.4d'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%.4d' '%.4d' '%.4d' '%.4d'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%04d");
    begin
      String s = sprintf("Integer '%04d' '%04d' '%04d' '%04d'", i1, i2, i3, i4);
      $display("%s", s);

      s = sprintf("Bit     '%04d' '%04d' '%04d'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%04d' '%04d' '%04d'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%04d' '%04d' '%04d' '%04d'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%*d");
    begin
      Integer sz = 5;
      String s = sprintf("Integer '%*d' '%*d' '%*d' '%*d'", sz, i1, sz, i2, sz, i3, sz, i4);
      $display("%s", s);

      s = sprintf("Bit     '%*d' '%*d' '%*d'", sz, b1, sz, b2, sz, b3);
      $display("%s", s);

      s = sprintf("UInt    '%*d' '%*d' '%*d'", sz, ub1, sz, ub2, sz, ub3);
      $display("%s", s);

      s = sprintf("Int     '%*d' '%*d' '%*d' '%*d'", sz, ib1, sz, ib2, sz, ib3, sz, ib4);
      $display("%s", s);
    end

    $display("#---- %%o");
    begin
      String s = sprintf("Integer '%o' '%o' '%o'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%o' '%o' '%o'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%o' '%o' '%o'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%o' '%o' '%o' '%o'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%O");
    begin
      String s = sprintf("'%O' '%O' '%O'", i1, i2, i3);
      $display("%s", s);
    end

    $display("#---- %%-8o");
    begin
      String s = sprintf("Integer '%-8o' '%-8o' '%-8o'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%-8o' '%-8o' '%-8o'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%-8o' '%-8o' '%-8o'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%-8o' '%-8o' '%-8o' '%-8o'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%4o");
    begin
      String s = sprintf("Integer '%4o' '%4o' '%4o'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%4o' '%4o' '%4o'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%4o' '%4o' '%4o'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%4o' '%4o' '%4o' '%4o'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%.4o");
    begin
      String s = sprintf("Integer '%.4o' '%.4o' '%.4o'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%.4o' '%.4o' '%.4o'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%.4o' '%.4o' '%.4o'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%.4o' '%.4o' '%.4o' '%.4o'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%04o");
    begin
      String s = sprintf("Integer '%04o' '%04o' '%04o'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%04o' '%04o' '%04o'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%04o' '%04o' '%04o'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%04o' '%04o' '%04o' '%04o'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%*o");
    begin
      Integer sz = 5;
      String s = sprintf("Integer '%*o' '%*o' '%*o'", sz, i1, sz, i2, sz, i3);
      $display("%s", s);

      s = sprintf("Bit     '%*o' '%*o' '%*o'", sz, b1, sz, b2, sz, b3);
      $display("%s", s);

      s = sprintf("UInt    '%*o' '%*o' '%*o'", sz, ub1, sz, ub2, sz, ub3);
      $display("%s", s);

      s = sprintf("Int     '%*o' '%*o' '%*o' '%*o'", sz, ib1, sz, ib2, sz, ib3, sz, ib4);
      $display("%s", s);
    end

    $display("#---- %%x");
    begin
      String s = sprintf("Integer '%x' '%x' '%x'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%x' '%x' '%x'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%x' '%x' '%x'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%x' '%x' '%x' '%x'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%X");
    begin
      String s = sprintf("'%X' '%X' '%X'", i1, i2, i3);
      $display("%s", s);
    end

    $display("#---- %%h");
    begin
      String s = sprintf("'%h' '%h' '%h'", i1, i2, i3);
      $display("%s", s);
    end

    $display("#---- %%H");
    begin
      String s = sprintf("'%H' '%H' '%H'", i1, i2, i3);
      $display("%s", s);
    end

    $display("#---- %%-8x");
    begin
      String s = sprintf("Integer '%-8x' '%-8x' '%-8x'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%-8x' '%-8x' '%-8x'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%-8x' '%-8x' '%-8x'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%-8x' '%-8x' '%-8x' '%-8x'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%4x");
    begin
      String s = sprintf("Integer '%4x' '%4x' '%4x'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%4x' '%4x' '%4x'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%4x' '%4x' '%4x'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%4x' '%4x' '%4x' '%4x'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%.4x");
    begin
      String s = sprintf("Integer '%.4x' '%.4x' '%.4x'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%.4x' '%.4x' '%.4x'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%.4x' '%.4x' '%.4x'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%.4x' '%.4x' '%.4x' '%.4x'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%04x");
    begin
      String s = sprintf("Integer '%04x' '%04x' '%04x'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%04x' '%04x' '%04x'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%04x' '%04x' '%04x'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%04x' '%04x' '%04x' '%04x'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%*x");
    begin
      Integer sz = 5;
      String s = sprintf("Integer '%*x' '%*x' '%*x'", sz, i1, sz, i2, sz, i3);
      $display("%s", s);

      s = sprintf("Bit     '%*x' '%*x' '%*x'", sz, b1, sz, b2, sz, b3);
      $display("%s", s);

      s = sprintf("UInt    '%*x' '%*x' '%*x'", sz, ub1, sz, ub2, sz, ub3);
      $display("%s", s);

      s = sprintf("Int     '%*x' '%*x' '%*x' '%*x'", sz, ib1, sz, ib2, sz, ib3, sz, ib4);
      $display("%s", s);
    end

    Real r1 = 0.0;
    Real r2 = - 1.7;
    Real r3 = 10 / 3;
    Real r4 = -1e23 / 8;
    Real r5 = 12345e-20;

    $display("#---- %%f %%F");
    begin
      String s = sprintf("'%.16f' '%.16f' '%.16f' '%.16f' '%.16f'", r1, r2, r3, r4, r5);
      $display("%s", s);

      s = sprintf("'%F' '%F' '%F' '%F' '%F'", r1, r2, r3, r4, r5);
      $display("%s", s);
    end

    $display("#---- %%e %%E");
    begin
      String s = sprintf("'%e' '%e' '%e' '%e' '%e'", r1, r2, r3, r4, r5);
      $display("%s", s);

      s = sprintf("'%E' '%E' '%E' '%E' '%E'", r1, r2, r3, r4, r5);
      $display("%s", s);
    end

    $display("#---- %%g %%G");
    begin
      String s = sprintf("'%g' '%g' '%g' '%g' '%g'", r1, r2, r3, r4, r5);
      $display("%s", s);

      s = sprintf("'%G' '%G' '%G' '%G' '%G'", r1, r2, r3, r4, r5);
      $display("%s", s);
    end

    $display("#---- %%.6f %%.6F");
    begin
      String s = sprintf("'%.6f' '%.6f' '%.6f' '%.6f' '%.6f'", r1, r2, r3, r4, r5);
      $display("%s", s);

      s = sprintf("'%.6F' '%.6F' '%.6F' '%.6F' '%.6F'", r1, r2, r3, r4, r5);
      $display("%s", s);
    end

    $display("#---- %%.6e %%.6E");
    begin
      String s = sprintf("'%.6e' '%.6e' '%.6e' '%.6e' '%.6e'", r1, r2, r3, r4, r5);
      $display("%s", s);

      s = sprintf("'%.6E' '%.6E' '%.6E' '%.6E' '%.6E'", r1, r2, r3, r4, r5);
      $display("%s", s);
    end

    $display("#---- %%*.*f %%*.*F");
    begin
      Integer p = 8;
      Integer q = 3;
      String s = sprintf("'%*.*f' '%*.*f' '%*.*f' '%*.*f' '%*.*f'",
                         p, q, r1, p, q, r2, p, q, r3, p, q, r4, p, q, r5);
      $display("%s", s);

      s = sprintf("'%*.*F' '%*.*F' '%*.*F' '%*.*F' '%*.*F'",
                  p, q, r1, p, q, r2, p, q, r3, p, q, r4, p, q, r5);
      $display("%s", s);
    end

    $display("#---- %%*.*e %%*.*E");
    begin
      Integer p = 10;
      Integer q = 3;
      String s = sprintf("'%*.*e' '%*.*e' '%*.*e' '%*.*e' '%*.*e'",
                         p, q, r1, p, q, r2, p, q, r3, p, q, r4, p, q, r5);
      $display("%s", s);

      s = sprintf("'%*.*E' '%*.*E' '%*.*E' '%*.*E' '%*.*E'",
                  p, q, r1, p, q, r2, p, q, r3, p, q, r4, p, q, r5);
      $display("%s", s);
    end

    $display("#---- %%b");
    begin
      String s = sprintf("Integer '%b' '%b' '%b'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%b' '%b' '%b'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%b' '%b' '%b'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%b' '%b' '%b' '%b'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%B");
    begin
      String s = sprintf("'%B' '%B' '%B'", i1, i2, i3);
      $display("%s", s);
    end

    $display("#---- %%-8b");
    begin
      String s = sprintf("Integer '%-8b' '%-8b' '%-8b'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%-8b' '%-8b' '%-8b'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%-8b' '%-8b' '%-8b'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%-8b' '%-8b' '%-8b' '%-8b'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%6b");
    begin
      String s = sprintf("Integer '%6b' '%6b' '%6b'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%6b' '%6b' '%6b'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%6b' '%6b' '%6b'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%6b' '%6b' '%6b' '%6b'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%.6b");
    begin
      String s = sprintf("Integer '%.6b' '%.6b' '%.6b'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%.6b' '%.6b' '%.6b'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%.6b' '%.6b' '%.6b'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%.6b' '%.6b' '%.6b' '%.6b'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%06b");
    begin
      String s = sprintf("Integer '%06b' '%06b' '%06b'", i1, i2, i3);
      $display("%s", s);

      s = sprintf("Bit     '%06b' '%06b' '%06b'", b1, b2, b3);
      $display("%s", s);

      s = sprintf("UInt    '%06b' '%06b' '%06b'", ub1, ub2, ub3);
      $display("%s", s);

      s = sprintf("Int     '%06b' '%06b' '%06b' '%06b'", ib1, ib2, ib3, ib4);
      $display("%s", s);
    end

    $display("#---- %%*b");
    begin
      Integer sz = 5;
      String s = sprintf("Integer '%*b' '%*b' '%*b'", sz, i1, sz, i2, sz, i3);
      $display("%s", s);

      s = sprintf("Bit     '%*b' '%*b' '%*b'", sz, b1, sz, b2, sz, b3);
      $display("%s", s);

      s = sprintf("UInt    '%*b' '%*b' '%*b'", sz, ub1, sz, ub2, sz, ub3);
      $display("%s", s);

      s = sprintf("Int     '%*b' '%*b' '%*b' '%*b'", sz, ib1, sz, ib2, sz, ib3, sz, ib4);
      $display("%s", s);
    end

    done <= True;
   endrule

   rule do_finish( done );
      $finish(0);
   endrule

endmodule
