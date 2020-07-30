package WallaceServer;

import GetPut::*;

import ClientServer::*;

import List::*;

import ListN::*;

// Type definition for a Wallace adder that takes l m-bit numbers and adds
// them to produce an n-bit result
// Remember (Add m k n) - i.e. at least as many bits in the result as in the 
// starting ListN
typedef Server#(ListN#(l , Bit#(m)), Bit#(n)) WallaceServer#(type l, type m, type n);

// A client of a Wallace adder
typedef Client#(ListN#(l, Bit#(m)), Bit#(n)) WallaceClient#(type l, type m, type n);

endpackage
