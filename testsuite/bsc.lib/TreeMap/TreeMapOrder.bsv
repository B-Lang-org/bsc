import TreeMap::*;

// Insert in reverse alphabetical order to exercise all four balance cases,
// then verify every key is still reachable and size is correct.
(* synthesize *)
module sysTreeMapOrder();
  TreeMap#(String, Integer) m0 = empty;
  TreeMap#(String, Integer) m1 = insert("elderberry", 5, m0);
  TreeMap#(String, Integer) m2 = insert("date",       4, m1);
  TreeMap#(String, Integer) m3 = insert("cherry",     3, m2);
  TreeMap#(String, Integer) m4 = insert("banana",     2, m3);
  TreeMap#(String, Integer) m  = insert("apple",      1, m4);

  rule test;
    $display("size: %0d", size(m));
    if (member("apple",      m)) $display("apple: found");      else $display("apple: missing");
    if (member("banana",     m)) $display("banana: found");     else $display("banana: missing");
    if (member("cherry",     m)) $display("cherry: found");     else $display("cherry: missing");
    if (member("date",       m)) $display("date: found");       else $display("date: missing");
    if (member("elderberry", m)) $display("elderberry: found"); else $display("elderberry: missing");
    if (member("fig",        m)) $display("fig: found");        else $display("fig: missing");
    $finish(0);
  endrule
endmodule
