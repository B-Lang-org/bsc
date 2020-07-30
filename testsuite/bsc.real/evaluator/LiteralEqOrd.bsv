(* synthesize *)
module sysLiteralEqOrd();
    Real w = 1.2;
    Real x = 1.1;
    Real y = 1.2;
    Real z = 1.3;
    Real v = 1;

    function m(s) = $display(message(s,s));

    rule r;
      if (w == y)
	m("w == y");
      if (w != y)
	m("ERROR: w != y");

      if (w < x)
	m("ERROR: w < x");
      if (w > x)
	m("w > x");

      if (w <= z)
	m("w <= z");
      if (w >= z)
	m("ERROR: w >= z");

      if (w < v)
	m("ERROR: w < v");
      if (w > v)
	m("w > v");
    endrule
endmodule