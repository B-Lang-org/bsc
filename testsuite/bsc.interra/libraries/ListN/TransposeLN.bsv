package TransposeLN;

import ListN :: *;

module mkTestbench_TransposeLN();

   ListN #(5,Int #(8)) my_list1 = cons (0, cons (1, cons (2, cons (3, cons (4, nil)))));
   ListN #(5,Int #(8)) my_list2 = cons (5, cons (6, cons (7, cons (8, cons (9, nil)))));
   ListN #(5,Int #(8)) my_list3 = cons (10, cons (11, cons (12, cons (13, cons (14, nil)))));

   List #(Int #(8)) my_list1_t = Cons (0, Cons (5, Cons (10, Nil)));
   List #(Int #(8)) my_list2_t = Cons (1, Cons (6, Cons (11, Nil)));
   List #(Int #(8)) my_list3_t = Cons (2, Cons (7, Cons (12, Nil)));
   List #(Int #(8)) my_list4_t = Cons (3, Cons (8, Cons (13, Nil)));
   List #(Int #(8)) my_list5_t = Cons (4, Cons (9, Cons (14, Nil)));

   List #(ListN#(5,Int #(8))) my_list4 = Cons (my_list1, Cons (my_list2, Cons (my_list3, Nil)));
   ListN #(5,List#(Int #(8))) my_list5 = cons (my_list1_t, cons (my_list2_t, cons (my_list3_t, cons (my_list4_t, cons (my_list5_t,nil)))));

   ListN #(5,List#(Int #(8))) my_list6 = transposeLN(my_list4);


   rule fire_once (True);
      if (my_list5 != my_list6)
        $display ("Simulation Fails");
      else
        $display ("Simulation Passes");
	  $finish(2'b00);
   endrule 
      
endmodule : mkTestbench_TransposeLN
endpackage : TransposeLN
