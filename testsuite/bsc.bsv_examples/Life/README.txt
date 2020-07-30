The Life example is based on John Conway's "Game of Life"

http://www.bitstorm.org/gameoflife/

THE GAME

The Game of Life is not your typical computer game. It is a 'cellular
automaton', and was invented by Cambridge mathematician John Conway.

This game became widely known when it was mentioned in an article published by
Scientific American in 1970. It consists of a collection of cells which, based
on a few mathematical rules, can live, die or multiply. Depending on the
initial conditions, the cells form various patterns throughout the course of
the game.

THE RULES

For a space that is 'populated':
    Each cell with one or no neighbors dies, as if by loneliness. 
    Each cell with four or more neighbors dies, as if by overpopulation. 
    Each cell with two or three neighbors survives. 
For a space that is 'empty' or 'unpopulated'
    Each cell with three neighbors becomes populated. 


THE BLUESPEC IMPLEMENTATION

The core module in this Bluespec example is "mkLife", which implements a m by
n grid, and the m by n cellular automatons.  Each cell is identical to its
neighbor, except for the edge cells which do not have 8 neighbors.  Each cell
(type Cell) is a register holding type Bool. As this is a synchronous design,
there is one rule "cycle" which triggers action "a".  Action "a" is generated
during static elaboration as a composite of each cell's action to "deaden" or
"enliven".

The interface has 2 methods; the first "set_pattern" sets a new pattern (n by
m) onto the grid.  The second one reloads a register "nextPattern" which
controls the update times.  This feature will be needed if/when there is a
display feature of this model.

At the testbench level, there is a module "sysLife" which instantiates a 5 by
5 grid, loads a pattern, and simulates for 100 generations, displaying the
pattern at each step.  This model could be generalized to support other sizes.

For synthesis and performance testing, there are a number of other
modules which instantiate various size grids, eg. mkLife77, etc.
