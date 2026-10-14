import TreeMap::*;

(* synthesize *)
module sysTreeMapLookup();
  TreeMap#(String, Integer) m0 = empty;
  TreeMap#(String, Integer) m1 = insert("banana", 2, m0);
  TreeMap#(String, Integer) m2 = insert("apple", 1, m1);
  TreeMap#(String, Integer) m  = insert("cherry", 3, m2);

  rule test;
    case (lookup("apple", m)) matches
      tagged Valid .v: $display("apple -> %0d", v);
      tagged Invalid:  $display("apple -> not found");
    endcase
    case (lookup("banana", m)) matches
      tagged Valid .v: $display("banana -> %0d", v);
      tagged Invalid:  $display("banana -> not found");
    endcase
    case (lookup("cherry", m)) matches
      tagged Valid .v: $display("cherry -> %0d", v);
      tagged Invalid:  $display("cherry -> not found");
    endcase
    case (lookup("durian", m)) matches
      tagged Valid .v: $display("durian -> %0d", v);
      tagged Invalid:  $display("durian -> not found");
    endcase
    case (lookup("apple", singleton("apple", 42))) matches
      tagged Valid .v: $display("singleton apple -> %0d", v);
      tagged Invalid:  $display("singleton apple -> not found");
    endcase
    $finish(0);
  endrule
endmodule
