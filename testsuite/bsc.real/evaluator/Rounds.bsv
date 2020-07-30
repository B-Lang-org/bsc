import Real::*;

(* synthesize *)
module sysRounds();
    Real r1 = 1.1;
    Real r2 = 1.5;
    Real r3 = 1.7;

    Integer w1 = round(r1);
    Integer x1 = ceil(r1);
    Integer y1 = floor(r1);
    Integer z1 = trunc(r1);

    Integer w2 = round(r2);
    Integer x2 = ceil(r2);
    Integer y2 = floor(r2);
    Integer z2 = trunc(r2);

    Integer w3 = round(r3);
    Integer x3 = ceil(r3);
    Integer y3 = floor(r3);
    Integer z3 = trunc(r3);

    // and the same for negative values
    Real nr1 = -1.1;
    Real nr2 = -1.5;
    Real nr3 = -1.7;

    Integer nw1 = round(nr1);
    Integer nx1 = ceil(nr1);
    Integer ny1 = floor(nr1);
    Integer nz1 = trunc(nr1);

    Integer nw2 = round(nr2);
    Integer nx2 = ceil(nr2);
    Integer ny2 = floor(nr2);
    Integer nz2 = trunc(nr2);

    Integer nw3 = round(nr3);
    Integer nx3 = ceil(nr3);
    Integer ny3 = floor(nr3);
    Integer nz3 = trunc(nr3);

    function m(s) = $display(message(s,s));

    rule r;
      m("round 1.1 = " + integerToString(w1));
      m("ceil  1.1 = " + integerToString(x1));
      m("floor 1.1 = " + integerToString(y1));
      m("trunc 1.1 = " + integerToString(z1));

      m("round 1.5 = " + integerToString(w2));
      m("ceil  1.5 = " + integerToString(x2));
      m("floor 1.5 = " + integerToString(y2));
      m("trunc 1.5 = " + integerToString(z2));

      m("round 1.7 = " + integerToString(w3));
      m("ceil  1.7 = " + integerToString(x3));
      m("floor 1.7 = " + integerToString(y3));
      m("trunc 1.7 = " + integerToString(z3));

      m("round -1.1 = " + integerToString(nw1));
      m("ceil  -1.1 = " + integerToString(nx1));
      m("floor -1.1 = " + integerToString(ny1));
      m("trunc -1.1 = " + integerToString(nz1));

      m("round -1.5 = " + integerToString(nw2));
      m("ceil  -1.5 = " + integerToString(nx2));
      m("floor -1.5 = " + integerToString(ny2));
      m("trunc -1.5 = " + integerToString(nz2));

      m("round -1.7 = " + integerToString(nw3));
      m("ceil  -1.7 = " + integerToString(nx3));
      m("floor -1.7 = " + integerToString(ny3));
      m("trunc -1.7 = " + integerToString(nz3));

    endrule
endmodule