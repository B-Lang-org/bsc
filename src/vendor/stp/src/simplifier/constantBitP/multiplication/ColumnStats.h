/*
 * ColumnStats.h
 *
 *  Created on: 24/03/2010
 *      Author: thansen
 */

#ifndef COLUMNSTATS_H_
#define COLUMNSTATS_H_

namespace simplifier
{
  namespace constantBitP
  {

    extern const bool debug_multiply;

    struct ColumnStats
    {
      int columnUnfixed; // both unfixed.
      int columnOneFixed; // one of the values is fixed to one, the other is unfixed.
      int columnOnes; // both are fixed to one.
      int columnZeroes; // one is fixed to zero.

      ColumnStats(const FixedBits & x, const FixedBits & y, int index)
      {
        columnUnfixed = 0;
        columnOneFixed = 0;
        columnOnes = 0;
        columnZeroes = 0;

        assert(index < x.getWidth());
        assert(y.getWidth() == x.getWidth());

        if (debug_multiply)
          log << "ColumnStats" << index << " " << x << " " << y << endl;

        for (unsigned i = 0; i <= (unsigned) index; i++)
          {
          bool xIsFixed = x.isFixed(index - i);
          bool yIsFixed;

          if (xIsFixed && !x.getValue(index - i))
            columnZeroes++;
          else if ((yIsFixed = y.isFixed(i)) && !y.getValue(i))
            columnZeroes++;
          else if (xIsFixed && x.getValue(index - i) && yIsFixed && y.getValue(i))
            columnOnes++;
          else if (yIsFixed && y.getValue(i))
            columnOneFixed++;
          else if (xIsFixed && x.getValue(index - i))
            columnOneFixed++;
          else
            columnUnfixed++;
          }

        assert(columnOnes >= 0 && columnUnfixed >= 0 && columnZeroes >= 0 && columnOneFixed >= 0);
        assert(columnOnes + columnUnfixed + columnOneFixed + columnZeroes == (index + 1));
      }

    };

    std::ostream&
    operator<<(std::ostream& o, const ColumnStats& cs)
    {
      o << "cUnfixed:" << cs.columnUnfixed << endl; // both unfixed.
      o << "cOneFixed:" << cs.columnOneFixed << endl; // one of the values is fixed to one.
      o << "cOnes:" << cs.columnOnes << endl;
      o << "cZero:" << cs.columnZeroes << endl;
      return o;
    }
  }
}

#endif /* COLUMNSTATS_H_ */
