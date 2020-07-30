package JoinRules;

import List :: *;


module mkTestbench_JoinRules (Empty);
      
      
      Rules r1 = rules 
                    rule print1 (True);
                      $display ("Simulation Passes");
                      $finish (2'b00);
                    endrule
                  endrules;
      Rules r2 = rules
                    rule print2 (True);
                      noAction;
                   endrule
                 endrules;
      Rules r3 = rules 
                    rule print1 (False);
                      $display ("Simulation Fails");
                      $finish(2'b00);
                    endrule
                  endrules;

      List #(Rules) my_list = Cons(r2, Cons(r1, Cons (r3, nil)));
     
      addRules (joinRules (my_list));
      

endmodule : mkTestbench_JoinRules

endpackage : JoinRules
