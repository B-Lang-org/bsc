import TreeMap::*;

(* synthesize *)
module sysTreeMapMember();
  TreeMap#(String, Integer) mt = empty;
  TreeMap#(String, Integer) m1 = insert("banana", 2, mt);
  TreeMap#(String, Integer) m2 = insert("apple", 1, m1);
  TreeMap#(String, Integer) m  = insert("cherry", 3, m2);

  rule test;
    if (member("apple", m))
      $display("apple: member");
    else
      $display("apple: not member");
    if (member("durian", m))
      $display("durian: member");
    else
      $display("durian: not member");
    if (isEmpty(mt))
      $display("empty is empty");
    else
      $display("empty is not empty");
    if (isEmpty(m))
      $display("m is empty");
    else
      $display("m is not empty");
    $display("size: %0d", size(m));
    $display("size empty: %0d", size(mt));
    $finish(0);
  endrule
endmodule
