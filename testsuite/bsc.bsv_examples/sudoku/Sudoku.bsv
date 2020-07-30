import Vector::*;
import StmtFSM::*;

import TypeUtil::*;
import SatMath::*;

// Some vocabulary:
//
// A sudoku grid consists of a number of cells, and these cells
// can be grouped into rows, columns, or boxes for the purposes
// of applying the uniqueness constraint within the group.
//
// The order of a sudoku puzzle is an integer > 1 such that
// each box of the grid is an order * order square of cells,
// and the entire grid is an order * order square of boxes.
// Thus each row, box and column contains order^2 cells and
// the entire grid contains order^4 cells.
//
// The boxes of a sudoku grid are identified by rank and file.
// A rank is a group of boxes which span the grid horizontally.
// A file is a group of boxes which span the grid vertically.
// The are order boxes in each rank and in each file, and order
// total ranks and order total files.
//
// For example, a typical order-3 sudoku grid contains 81 cells
// which can be grouped into 9 rows of 9 cells each, 9 columns
// of 9 cells each, or 9 3x3 boxes of cells.  The boxes form 3
// ranks (each rank consists of 3 boxes arranged horizontally)
// and 3 files (each file consists of 3 boxes stacked vertically).

// A sudoku cell for a given order contains a bit mask of
// order^2 bits.  When bit[n] is set, it indicates that the
// value n+1 has not been ruled out for that cell.
typedef Bit#(TSquare#(order)) Cell#(numeric type order);

function Cell#(order) unknown();
   return '1;   // all values are possible
endfunction: unknown

function Cell#(order) impossible();
   return '0;   // no value is possible
endfunction: impossible

function Cell#(order) given(UInt#(n) x)
   provisos(Mul#(order, order, size), Log#(size, index_bits),
	    Log#(TAdd#(1,size), n));
   Index#(order) idx = unpack(pack(x-1)[valueOf(index_bits)-1:0]);
   return (1 << idx);
endfunction: given

// A cell has a uniquely determined value if it has exactly one bit set.
function Bool isComplete(Cell#(order) c) provisos(Add#(1,_,TSquare#(order)));
   UInt#(2) count = fold(addSat(2), map(boolToSat, bitsToVector(c)));
   return (count == 1);
endfunction: isComplete

// A cell with one bit set has a value equal to the index of the set
// bit.  If there is not exactly one bit set, then the cell has no
// value.
function Maybe#(UInt#(value_bits)) cellValue(Cell#(order) c)
   provisos(Mul#(order,order,size), Log#(size,value_bits));
   Maybe#(UInt#(value_bits)) v = Invalid;
   for (Integer i = 0; i < valueOf(size); i = i + 1)
   begin
      if (c == (1 << i)) v = Valid(fromInteger(i));
   end
   return v;
endfunction: cellValue

// This is similar to cellValue, except that it returns a value
// in the range of 1 to size inclusive, used for display to the
// user.
function Maybe#(UInt#(value_bits)) cellValueUser(Cell#(order) c)
   provisos(Mul#(order,order,size), Log#(TAdd#(size,1),value_bits));
   Maybe#(UInt#(value_bits)) v = Invalid;
   for (Integer i = 0; i < valueOf(size); i = i + 1)
   begin
      if (c == (1 << i)) v = Valid(fromInteger(i+1));
   end
   return v;
endfunction: cellValueUser

// A Grid is a vector of vectors of some type.
typedef Vector#(rows, Vector#(cols, t))
        Grid#(numeric type rows, numeric type cols, type t);

// A SudokuRegGrid is a sudoku-style grid of registers containing
// cells, paramaterized by the order of the sudoku puzzle.
typedef Reg#(Grid#(TSquare#(order), TSquare#(order), Cell#(order)))
        SudokuRegGrid#(numeric type order);

// Convert a box number and an index within the box to an index in the grid
function Index#(order) boxToGrid(RFIndex#(order) bi, RFIndex#(order) ci)
   provisos(Add#(_,TLog#(order),TLog#(TSquare#(order))));   
   return (zeroExtend(bi) * (fromInteger(valueOf(order))) + zeroExtend(ci));
endfunction: boxToGrid

// Convert an index into the grid to a rank or file index
function RFIndex#(order) gridToRF(Index#(order) i)
   provisos(Add#(_,TLog#(order),TLog#(TSquare#(order))));
   return truncate(i / (fromInteger(valueOf(order))));
endfunction: gridToRF

// Convert an index into the grid to an index into the containing box
function RFIndex#(order) gridToBox(Index#(order) i)
   provisos(Add#(_,TLog#(order),TLog#(TSquare#(order))));
   return truncate(i % (fromInteger(valueOf(order))));
endfunction: gridToBox

// Convert an index into the grid to an index into the containing box
// represented as a Group.
function Index#(order) gridToBoxGroup(Index#(order) r, Index#(order) c);
   let n = fromInteger(valueOf(order));
   return ((r % n) * n) + (c % n);
endfunction: gridToBoxGroup

// This is used as row and column indices
typedef UInt#(TLog#(TSquare#(order))) Index#(numeric type order);

// This is used as rank/file indices and to index cells in a box
typedef UInt#(TLog#(order)) RFIndex#(numeric type order);

// Similar types which may have an extra bit for use as loop indices
typedef UInt#(TLog#(TAdd#(1,TSquare#(order)))) LIndex#(numeric type order);
typedef UInt#(TLog#(TAdd#(1,order))) LRFIndex#(numeric type order);

function Index#(order) l2i(LIndex#(order) n)
   provisos(Mul#(order,order,size), Log#(size,index_bits));
   return unpack(pack(n)[valueOf(index_bits)-1:0]);
endfunction

function RFIndex#(order) l2rfi(LRFIndex#(order) n)
   provisos(Log#(order,index_bits));
   return unpack(pack(n)[valueOf(index_bits)-1:0]);
endfunction

// A Group can contain a constraint group - a row, column or box
typedef Vector#(TSquare#(order), Cell#(order)) Group#(numeric type order);

// Functions for extracting cell groups from a SudokuRegGrid

function Cell#(order) getCell(SudokuRegGrid#(order) g, Index#(order) r, Index#(order) c);
   return g[r][c];
endfunction: getCell

function Group#(order) getRow(SudokuRegGrid#(order) g, Index#(order) r);
   return g[r];
endfunction: getRow

function Group#(order) getColumn(SudokuRegGrid#(order) g, Index#(order) c);
   let col = zipWith(select, g, replicate(c));
   return col;
endfunction: getColumn

function Group#(order) getBox(SudokuRegGrid#(order) g, RFIndex#(order) r, RFIndex#(order) f)
   provisos(Add#(_,TLog#(order),TLog#(TSquare#(order))));   
   function Index#(order) to_row(Integer n);
      return boxToGrid(r,fromInteger(n/valueOf(order)));
   endfunction: to_row
   function Index#(order) to_col(Integer n);
      return boxToGrid(f,fromInteger(n%valueOf(order)));
   endfunction: to_col
   Vector#(size,Index#(order)) rows = genWith(to_row);
   Vector#(size,Index#(order)) cols = genWith(to_col);
   return zipWith(getCell(g), rows, cols);
endfunction: getBox

// Debug / display utilities

function Action displayCharSmall(function Cell#(o) get(Index#(o) r, Index#(o) c),
				 UInt#(16) x, UInt#(16) y)
   provisos(Add#(a,TLog#(TSquare#(o)),16),
            Add#(b,TLog#(TAdd#(TSquare#(o),1)),16));
   action
      let h_period = 2*valueOf(o)+1;
      let v_period = valueOf(o)+1;
      let vert_line  = ((x % fromInteger(h_period)) == 0);
      let horiz_line = ((y % fromInteger(v_period)) == 0);
      let eol = (x == fromInteger(h_period*valueOf(o)));
      Index#(o) c = truncate((x - 1 - (x/fromInteger(h_period))) / 2);
      Index#(o) r = truncate(y - 1 - (y/fromInteger(v_period)));
      let first_digit = (((x - 1 - (x/fromInteger(h_period))) % 2) == 0);
      if (vert_line && horiz_line) $write("+");
      else if (vert_line) $write("|");
      else if (horiz_line) $write("-");
      else if (first_digit)
      begin
	 UInt#(16) v = extend(fromMaybe(0,cellValueUser(get(r,c)))) / 10;
	 if (v > 0)
	    $write("%1d", v);
	 else
	    $write(" ");
      end
      else
      begin
	 UInt#(16) v = extend(fromMaybe(0,cellValueUser(get(r,c))));
	 if (v > 0)
	    $write("%1d", v % 10);
	 else
	    $write(" ");
      end
      if (eol) $display();  // newline
   endaction
endfunction: displayCharSmall

function Action displayCharLarge(function Cell#(o) get(Index#(o) r, Index#(o) c),
				 UInt#(16) x, UInt#(16) y)
   provisos(Add#(a,TLog#(TSquare#(o)),16),
            Add#(b,TLog#(TAdd#(TSquare#(o),1)),16));
   action
      let h_period = 2*valueOf(o)+1;
      let v_period = valueOf(o)+1;
      let vert_line  = ((x % fromInteger(h_period)) == 0);
      let horiz_line = ((y % fromInteger(v_period)) == 0);
      let thick_vert_line  = ((x % (fromInteger(h_period*valueOf(o)))) == 0);
      let thick_horiz_line = ((y % (fromInteger(v_period*valueOf(o)))) == 0);
      let eol = (x == fromInteger(h_period*valueOf(o)*valueOf(o)));
      Index#(o) c = truncate(x/fromInteger(h_period));
      Index#(o) r = truncate(y/fromInteger(v_period));
      Index#(o) n = truncate((((x%fromInteger(h_period)) - 1) / 2) +
			     (((y%fromInteger(v_period)) - 1) * fromInteger(valueOf(o))));
      let first_digit = ((((x%fromInteger(h_period))-1) % 2) == 0);
      if (vert_line && horiz_line) $write("+");
      else if (thick_vert_line) $write("*");
      else if (thick_horiz_line) $write("=");
      else if (vert_line) $write("|");
      else if (horiz_line) $write("-");
      else if (first_digit)
      begin
	 UInt#(16) v = (get(r,c)[n] == 1) ? ((extend(n)+1)/10) : 0;
	 if (v > 0)
	    $write("%1d", v);
	 else
	    $write(" ");
      end
      else
      begin
	 UInt#(16) v = (get(r,c)[n] == 1) ? (extend(n)+1) : 0;
	 if (v > 0)
	    $write("%1d", v % 10);
	 else
	    $write(" ");
      end
      if (eol) $display();  // newline
   endaction
endfunction: displayCharLarge

function Stmt displayGrid(UInt#(16) width, UInt#(16) height,
			  Reg#(UInt#(16)) x, Reg#(UInt#(16)) y,
			  function Action display(UInt#(16) x, UInt#(16) y));
   return (seq
	      for (y <= 0; y < height; y <= y + 1)
		 for (x <= 0; x < width; x <= x + 1)
		    display(x,y);
	   endseq);
endfunction: displayGrid
      
// Display a grid of Sudoku cells
function Stmt displaySudoku(function Cell#(o) get(Index#(o) r, Index#(o) c),
			    Reg#(UInt#(16)) x, Reg#(UInt#(16)) y)
   provisos(Add#(a,TLog#(TSquare#(o)),16),
            Add#(b,TLog#(TAdd#(TSquare#(o),1)),16));      
   let w = fromInteger((2*valueOf(o)+1)*valueOf(o)+1);
   let h = fromInteger((valueOf(o)+1)*valueOf(o)+1);   
   return displayGrid(w,h,asReg(x),asReg(y),displayCharSmall(get));
endfunction: displaySudoku
		    
function Stmt debugSudoku(function Cell#(o) get(Index#(o) r, Index#(o) c),
			  Reg#(UInt#(16)) x, Reg#(UInt#(16)) y)
   provisos(Add#(a,TLog#(TSquare#(o)),16),
            Add#(b,TLog#(TAdd#(TSquare#(o),1)),16));      
   let w = fromInteger((2*valueOf(o)+1)*valueOf(o)*valueOf(o)+1);
   let h = fromInteger((valueOf(o)+1)*valueOf(o)*valueOf(o)+1);   
   return displayGrid(w,h,asReg(x),asReg(y),displayCharLarge(get));
endfunction: debugSudoku
