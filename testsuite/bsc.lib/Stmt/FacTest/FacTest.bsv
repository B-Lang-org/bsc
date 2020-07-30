import StmtFSM :: * ;


// Define a typedef for our data
typedef Int#(32) Int32;
Int32 factLimit = 12 ;

(* synthesize *)
module mkFacTest ();

   Reg#(Int32) upper <- mkReg( 1 )  ;
   Reg#(Int32) i     <- mkRegU ;
   Reg#(Int32) prod  <- mkRegU ;   
   
   Stmt factorialSequence =
   seq
      action                    // One action take 1 clock step
         prod <= 1 ;         
         $display( "starting factorial Sequence; upper = %0d", upper ) ;
      endaction
      for ( i <= 2;  upper >= i ; i <= i + 1 )
         seq                    // sequence takes 1 clock per action
            prod <= prod * i ;
            $display( "i is %0d, prod is %0d", i, prod ) ;
         endseq
      $display( "factorial sequence is done: factorial of %0d is %0d", upper, prod ) ;
   endseq ;
   
   FSM mfac <- mkFSM( factorialSequence );

   rule doFactorial ( upper < factLimit ) ;
      upper <= 1 + upper ;
      mfac.start;
   endrule

   rule finisher ( (upper >= factLimit) && mfac.done ) ;
      $finish(0) ;
   endrule
   
endmodule



(* synthesize *)
module mkLockTest() ;

   Reg#(Int32) cntr  <- mkReg(0) ;
   
   Stmt parallelAction =
   seq
      $display( "starting parallel actions" ) ;
      par
      seq
         action            
            $display( "got the lock on a first path" ) ;
            $display( "counter is %0d", cntr ) ;
            cntr <= cntr + 10;
         endaction
         cntr <= cntr + 10 ;
         cntr <= cntr + 10 ;
         cntr <= cntr + 10 ;
         action
            $display( "releasing  the lock on a first path" ) ;
            $display( "counter is %0d", cntr ) ;
         endaction
      endseq
      seq
         action
            $display( "counter is %0d", cntr ) ;
            cntr <= cntr + 1;
         endaction
         cntr <= cntr + 1 ;
         cntr <= cntr + 1 ;
         cntr <= cntr + 1 ;
         action
            $display( "releasing  the lock on a second path" ) ;
            $display( "counter is %0d", cntr ) ;
         endaction
      endseq 
      endpar 
      $display( "finished parallel actions" ) ;
   endseq ;

   FSM pfsm <- mkFSM( parallelAction ) ;
   Once oneShotFSM <- mkOnce( pfsm.start ) ;

   rule shot ( True ) ;
      oneShotFSM.start ;
   endrule

   rule finisher ( pfsm.done && oneShotFSM.done ) ;
      $finish(0) ;
   endrule
endmodule


// --@ 
// --@ Parallel execution and locks:
// --@ {\small
// --@ \begin{verbatim}
// --@ Stmt party;
// --@ party = actionvalue
// --@ 	  Int32 i;
// --@ 	  i <- static(0);
// --@ 	  l <- mkLock;
// --@ 	  while(i < 100,
// --@ 		actionvalue
// --@ 		  par(actionvalue
// --@ 			seq(actionvalue
// --@ 			      lock(l);
// --@ 			      i += 1;
// --@ 			      i += 1;
// --@ 			      unlock(l);
// --@ 			    endactionvalue);
// --@ 			seq(actionvalue
// --@ 			      lock(l);
// --@ 			      i += 1;
// --@ 			      i += 1;
// --@ 			      i += 1;
// --@ 			      i += 1;
// --@ 			      unlock(l);
// --@ 			    endactionvalue);
// --@ 			seq(actionvalue
// --@ 			      lock(l);
// --@ 			      s($display("i=%0d", i));
// --@ 			      unlock(l);
// --@ 			    endactionvalue);
// --@ 		      endactionvalue);
// --@ 		endactionvalue);
// --@ 	endactionvalue;
// --@ \end{verbatim}
// --@ }
// {-
// party :: Stmt
// party = do {
//     i :: Int32 <- static 0;
//     l <- mkLock;

//     while (i < 100) do {
//         -- run 3 parallel subtasks
//         par do {
//             seq do {
//                 lock(l);
//                 i += 1; i += 1;
//                 unlock(l);
//             };
//             seq do {
//                 lock(l);
//                 i += 1; i += 1; i += 1; i += 1;
//                 unlock(l);
//             };
//             seq do {
//                 lock(l);
//                 s $ $display "i=%0d" i;
//                 unlock(l);
//             };
//         };
//     };
//  }

// partest :: Module Empty
// partest =
//     module
//         n :: Reg (Bit 32) <- mkReg 10
//         mpar <- stmtFSM party
//         o <- mkOnce mpar.start
//         rules
//             when True
//              ==> o.start
// -}
