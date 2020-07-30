import Vector::*;

typedef TMul#(x,x) TSquare#(numeric type x);

typedef Bit#(TSquare#(order)) Cell#(numeric type order);

function Cell#(order) unknown();
   return '1;   // all values are possible
endfunction: unknown

function Cell#(order) impossible();
   return '0;   // no value is possible
endfunction: impossible

function Bool isComplete(Cell#(order) c)
   provisos( Add#( 1, xxx, TLog#(TAdd#(1, TMul#(order,order)))));   
   return (countOnes(c) == 1);
endfunction: isComplete

typedef Vector#(rows, Vector#(cols, t))
        Grid#(numeric type rows, numeric type cols, type t);

typedef UInt#(TLog#(TSquare#(order))) Index#(numeric type order);

typedef Vector#(TSquare#(order), Cell#(order)) Group#(numeric type order);

typedef Vector#(TSquare#(order), Bool) Mask#(numeric type order);

function Group#(order) maskOne(Group#(order) g, Index#(order) n);
   return update(g,n,impossible());
endfunction: maskOne

function Bool is2set(Cell#(order) c)
   provisos( Add#( 1, xxx, TLog#(TAdd#(1, TMul#(order,order)))));
   return (countOnes(c) == 2);
endfunction: is2set
      
interface Tactics#(numeric type order);
   
   method Cell#(order) hidden_pair(Group#(order) g, Index#(order) n);
      
endinterface: Tactics

module mkTactics(Tactics#(order))
   provisos(Mul#(order,order,size), Add#(1,_,SizeOf#(Cell#(order))));
   method Cell#(order) hidden_pair(Group#(order) g, Index#(order) n);
      let g1 = maskOne(g,n);
      Cell#(order) out = unknown();
      for (Integer i = 1; i < valueOf(size); i = i + 1)
      begin
	 let common = g1[i] & g[n];   
//       Using this test gives large heap usage
//	 if (is2set(common))
//       Using this test gives a stack overflow	 
	 if (common != unknown())	 
	 begin
	    // commenting out this test (but leaving the
	    // assignment) makes AOpt fast.
	    if (common != impossible())
	       out = out & common;
	 end
      end
      return out;      
   endmethod: hidden_pair
 
endmodule: mkTactics

(* synthesize *)
module mkTactics4(Tactics#(4));
   Tactics#(4) _t <- mkTactics();
   return (_t);
endmodule: mkTactics4
