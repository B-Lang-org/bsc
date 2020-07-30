(* synthesize *)
module sysAssertTasks();

  rule dummy;
    $error();
    $error("foo", 15, "a %d", 6'hf);
    $info("bar", 23);
    $info();
    $warning("This is a warning", 13);
    $warning();
    $fatal();
    $fatal(0);
    $fatal(2, "Test", 5'b00100, "foo %m");
   endrule

endmodule
 