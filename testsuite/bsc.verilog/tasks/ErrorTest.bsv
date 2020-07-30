module sysErrorTest();

  rule test;
    $error("foo");
    $fatal(0, "bar");
  endrule

endmodule
