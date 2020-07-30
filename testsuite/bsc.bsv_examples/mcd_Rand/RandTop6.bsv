// imports, and ExtIfc definition, as before . . .

(* synthesize *)
module mkRandTop(Clock c0, Clock c1, Clock c2, ExtIfc);
   // Instantiate the three sub-modules as before, but now each with its own
   // clock: 
   GenPair gens();
   mkSplitter the_gens(gens, clocked_by c0);

   UserIfc user1();
   mkRUser1 the_user1(user1, clocked_by c1);

   UserIfc user2();
   mkRUser2 the_user2(user2, clocked_by c2);

   // Now the conversion logic.  We use the version of the conversion FIFO
   // with Get/Put interfaces, for easy connection.  Define two converters,
   // with the appropriate clocks for the Get and Put interfaces:
   GetPut#(Bit#(6)) conv_gp1();
   mkConvGetPut the_user1_converter(c1, c0, conv_gp1);
   GetPut#(Bit#(6)) conv_gp2();
   mkConvGetPut the_user2_converter(c2, c0, conv_gp2);

   // Now we can connect everything up, connecting the Get subinterface from
   // each converter to the Put from the corresponding user, and the
   // Put ones to the Get from gens, since the clocks for the pairs to be
   // connected together are now the same:
   mkConnection(conv_gp1.fst, user1.fst);
   mkConnection(conv_gp1.snd. gens.fst);
   
   mkConnection(conv_gp2.fst, user2.fst);
   mkConnection(conv_gp2.snd. gens.snd);

   // The appropriate interfaces are exported as before:
   interface ifcA = user1.snd;
   interface ifcB = user2.snd;
endmodule
