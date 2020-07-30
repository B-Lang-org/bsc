package Life;

// We import the Vector package explicitly, to have it available for
// definitions such as the next few.
import Vector::*;

// The element cell for the Life board:

typedef Reg#(Bool) Cell;

// For most purposes of this design, the Life board is a two-dimensional BSV
// array of Cells (see the definition of "board" below).  Actually this
// structure also doubles as a list of lists (in the Lisp or Haskell sense).
// But in order to make a complete board's contents a permissible data-item
// for the interface of a separately synthesized module, this has to be
// represented instead as a Vector of ListNs: this is because the compiler
// needs to be able to represent  the value in bits, and its size therefore
// has to be part of its type.  The following definitions define a Pattern
// accordingly; parameterized by the number of rows and columns on the board.

typedef Vector#(rsize, contents)              Row#(type rsize, type contents);
typedef Vector#(csize, Row#(rsize, contents)) Grid#(type rsize, type csize, type contents);
typedef Grid#(rsize, csize, Bool)            Pattern#(type rsize, type csize);

// The interface for the mkLife module, also parameterized by the size of the
// board.  The methods set the initial contents of the board, specify the
// cycle-count at which the board is next to be available for inspection, and
// to read out the contents at such moments.

interface Query #(type rsize, type csize);
   method Action set_pattern(Pattern#(rsize, csize) pattern);
   method Action set_nextMoment(Nat nextM);
   method Pattern#(rsize,csize) pattern();
endinterface 

// A Cell has eight neighbours; this type is used for the count of how many of
// them are alive:

typedef bit[2:0] NeighbourCount;
NeighbourCount defaultValue;
defaultValue = 0;

// There now follows the main module.  As its interface is parameterized on
// size, it cannot itself be separately synthesized.  Below, several versions
// with specific sizes are made available for synthesis.  (Note: the
// parametersa and b to Query are dummy parameters, to satisfy the
// type-checker.) 

module mkLife#(Integer sizeX, Integer sizeY)(Query#(a,b));
   
   // The board is declared, and initialized with a doubly-nested loop:
   
   List#(List#(Cell)) board = List::replicate(sizeX, List::replicate(sizeY, ?));
   for (Integer x = 0; x < sizeX; x = x+1)
      begin
	 for (Integer y = 0; y < sizeY; y = y+1)
            begin
               Cell c();
               mkReg#(False)the_cell(c);
               board[x][y] = asReg(c);
            end
      end
   
   // The following function identifies a particular Cell by its position, and
   // returns it as a register, so that it may be updated (rather than simply
   // returning its contents):
   
   function Reg#(Bool) find_cell(Integer x, Integer y);
      return (asReg(board[x][y]));
   endfunction

   // The following function says whether a particular Cell is alive or not,
   // also checking whether the requested Cell is off the board (in which case
   // it is assumed not alive):
   
   function NeighbourCount is_alive(Integer x, Integer y);
      NeighbourCount r;
      if (x < 0 || y < 0 || x >= sizeX || y >= sizeY)
	 r = defaultValue;
      else
	 begin
	    Cell c = find_cell(x,y);
	    r = (c ? 1 : 0);
	 end
      return r;
   endfunction

   // The action a is next defined, by accumulating it with a doubly-nested
   // loop.  For each Cell on the board, each of its neighbours is examined,
   // and the count formed of those which are alive.  Then, if appropriate, an
   // action to deaden or to enliven the Cell is added to the Action a.
   
   Action a = noAction;
   
   for (Integer x = 0; x < sizeX; x = x+1)
      for (Integer y = 0; y < sizeY; y = y+1)
         begin
	    Cell c = find_cell(x,y);
	    
            NeighbourCount up = is_alive(x,y-1);  
            NeighbourCount down = is_alive(x,y+1);
            NeighbourCount left = is_alive(x-1,y);
            NeighbourCount right = is_alive(x+1,y);
            NeighbourCount upleft = is_alive(x-1,y-1);
            NeighbourCount upright = is_alive(x+1,y-1);
            NeighbourCount downleft = is_alive(x-1,y+1);
            NeighbourCount downright = is_alive(x+1,y+1);
	    
	    NeighbourCount sum = up+down+left+right+
	    upleft+downleft+upright+downright;
	    
	    // The deadening action, if appropriate;
            let deaden  = (action
			      if (c && (sum < 3 || sum > 5))
				 c <= False;
			      else noAction;
			   endaction);

	    // The enlivening action, if appropriate:
            let enliven = (action
			      if (!c && (sum >= 3 && sum <= 5))
				 c <= True; 
			      else noAction;
			   endaction);

	    // These new actions are added to a.
            a = (action
                    a;
		    deaden;
		    enliven;
		 endaction);
         end

   // The register holding the cycle-count:
   Reg#(Nat) cnt();
   mkReg#(0) the_cnt(cnt);

   // The register holding the cycle-count at which the next inspection is due:
   Reg#(Nat) nextPattern();
   mkReg#(0) the_nextPattern(nextPattern);

   // At each cycle the Action a, defined above, is performed, and the count
   // incremented:
   rule cycle (cnt < nextPattern);
      action
         a;
         cnt <= cnt + 1;
      endaction
   endrule

   // Finally come the methods of the interface:
   
   // This method sets the board to the new pattern.  (Note that the double
   // loop here is performed at static elaboration time, so that at run time
   // the assignments to all the Cells happen in parallel.)
   method Action set_pattern(bss);
      action
	 for (Integer x = 0; x < sizeX; x = x+1)
	    for (Integer y = 0; y < sizeY; y = y+1)
               begin
		  (board[x][y]) <= bss[x][y];  
               end
      endaction
   endmethod
   
   // This method sets the moment at which the next inspection of the board
   // will fall due:
   method Action set_nextMoment(Nat x);
      action
	 nextPattern <= x;
      endaction
   endmethod

   // This method outputs the current contents of the board.  It is enabled
   // only at specified moments of inspection:
   method pattern() if (cnt == nextPattern);
      // A local function, to read the contents of a Cell:
      function Bool f(Cell r);
         return r;
      endfunction

      // a BSV array may be thought of as a list; so the board is a list of
      // lists of Cells.  The next definition uses the standard
      // list-processing function map to convert a board to a list of lists of
      // the cells' values:
      let res1 = List::map(List::map(f), board ) ;

      // map is again used, to convert res1 to type Pattern, as required for a
      // synthesizable interface:
      return toVector( List::map(toVector, res1)) ;
   endmethod          
endmodule

// Now follows the testbench, which exercises mkLife for a 5x5 board.

(* synthesize *)
module sysLife(Empty);

   // An interface for mkLife, at the required size, is declared, and used to
   // instantiate the corresponding version of mkLife (defined below):
   Query#(5,5) q_ifc();
   mkLife55 the_life(q_ifc);

   // A flag to tell whether the test has been started:
   Reg#(Bool) started();
   mkReg#(False) the_started(started);

   // The test's cycle count:
   Reg#(Nat) m();
   mkReg#(0) the_m(m);

   // The rule to initialise the test.  
   rule start (!started);
      action
	 started <= True;
	 
	 // An initial pattern is declared and initialised (the "unpack"
	 // converts the bit-vector to a Vector of Bools; the "toList" converts
	 // that to a BSV array (also known as a List):
	 List#(List#(Bool)) b = List::replicate(5, List::replicate(5, ?));
	 b[0] = toList(unpack(5'b00000)) ;
	 b[1] = toList(unpack(5'b00100) );
	 b[2] = toList(unpack(5'b01110) );
	 b[3] = toList(unpack(5'b00100) );
	 b[4] = toList(unpack(5'b00000) ) ;

	 // A loop to display the initial input:
	 $display("The input:");
	 for (Integer x = 0; x < 5; x = x+1)
            begin
               Vector#(5,Bool) column = toVector(b[x]) ;
               $display("%d: %b", x, column ) ;
            end
	 $display("\n");

	 // the array b is converted to a Vector of ListNs, again using map,
	 // and supplied as the argument to the method setting the initial
	 // contents of the board in the mkLife instantiation:
	 q_ifc.set_pattern(toVector( List::map(toVector,b) ));
	 // The time of the next inspection is set (to zero - this will enable
	 // us to check that the board has been correctly initialized:
	 q_ifc.set_nextMoment(m);
      endaction
   endrule

   // The rule to do periodic inspections as the evolution of the Life pattern
   // proceeds: 
   rule going (started && m<100);
      action
	 // Read the pattern (implicitly waiting for the next moment of
	 // inspection): 
	 Pattern#(5,5)  p = q_ifc.pattern;

	 // display the pattern, row by row:
	 $display("%d", m);
	 for (Integer x = 0; x < 5; x = x+1)
	    $display("%b", p[x]);
	 $display("\n");

	 // In this test we are inspecting the pattern after each cycle; so
	 // mkLife's cycle count and the testbench's are in step.  Set the
	 // count for the next required inspection:
	 q_ifc.set_nextMoment(m+1);
	 m <= m+1;
      endaction
   endrule  

   // Terminate the test after 100 cycles:
   rule stop (started && m == 100);
      action
	 $finish(0);
      endaction
   endrule
endmodule

// There finally follow several versions of mkLife, specialised to specific
// sizes.  The "synthesize" attribute is used to specify which of them should
// be synthesized to Verilog (or C):

(* synthesize *)
module mkLife55 (Query#(5,5) );
   Query#(5,5) q_ifc() ;
   mkLife#(5,5) life(q_ifc) ;
   
   return q_ifc;
endmodule

module mkLife77 (Query#(7,7) );
   Query#(7,7) q_ifc() ;
   mkLife#(7,7) life(q_ifc) ;
   
   return q_ifc;
endmodule
 

module mkLife1010 (Query#(10,10) );
   Query#(10,10) q_ifc() ;
   mkLife#(10,10) life(q_ifc) ;

   return q_ifc;
endmodule


module mkLife1515 (Query#(15,15) );
   Query#(15,15) q_ifc() ;
   mkLife#(15,15) life(q_ifc) ;

   return q_ifc;
endmodule


module mkLife2020 (Query#(20,20) );
   Query#(20,20) q_ifc() ;
   mkLife#(20,20) life(q_ifc) ;

   return q_ifc;
endmodule


module mkLife2525 (Query#(25,25) );
   Query#(25,25) q_ifc() ;
   mkLife#(25,25) life(q_ifc) ;

   return q_ifc;
endmodule


// The compiler currently needs about a gigabyte of RAM to synthesize an
// instantiation of this size:
module mkLife3030 (Query#(30,30) );
   Query#(30,30) q_ifc() ;
   mkLife#(30,30) life(q_ifc) ;

   return q_ifc;
endmodule

endpackage
