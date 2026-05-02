import TreeMap::*;

function Integer add(Integer x, Integer y);
  return x + y;
endfunction

(* synthesize *)
module sysTreeMapInsertWith();
  TreeMap#(String, Integer) m0 = empty;
  TreeMap#(String, Integer) m1 = insert(        "apple",  1, m0);
  TreeMap#(String, Integer) m2 = insertWith(add, "apple",  5, m1); // 1+5=6
  TreeMap#(String, Integer) m3 = insertWith(add, "banana", 3, m2); // new key
  TreeMap#(String, Integer) m  = insertWith(add, "apple", 10, m3); // 6+10=16

  rule test;
    case (lookup("apple", m)) matches
      tagged Valid .v: $display("apple -> %0d", v);
      tagged Invalid:  $display("apple -> not found");
    endcase
    case (lookup("banana", m)) matches
      tagged Valid .v: $display("banana -> %0d", v);
      tagged Invalid:  $display("banana -> not found");
    endcase
    $finish(0);
  endrule
endmodule
