import List::*;

(* synthesize *)
module sysSelectListActionUndefinedIndex();
  
  List#(Action) l = cons($display(1), 
                      cons($display(2), 
                       cons($display(3), 
                         cons($display(4), nil))));

  rule test;
    l[?];
  endrule

endmodule
