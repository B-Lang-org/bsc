(* synthesize *)
(* no_default_clock *)
module sysNoDefaultClock_Port#(Clock clk, Bool p)();
  Reg#(Bool) rg <- mkRegU(clocked_by clk);

  // This should not generate a multiple-clock error
  // because the port should be associated with no_clock
  // (or, even if a special missingDefaultClock is created,
  // if its domain is specified as noClockDomain, then there
  // would be no error because only the domains are checked)
  //
  rule r;
    rg <= p;
  endrule
endmodule
