/*
 * ColumnCounts.h
 *
 *  Created on: 24/03/2010
 *      Author: thansen
 */

#ifndef COLUMNCOUNTS_H_
#define COLUMNCOUNTS_H_

namespace simplifier
{
  namespace constantBitP
  {

    extern std::ostream& log;

    struct Interval
    {
      int& low;
      int& high;
      Interval(int& _low, int& _high) :
          low(_low), high(_high)
      {
      }
    };

    struct ColumnCounts
    {
      signed *columnH; // maximum number of true partial products.
      signed *columnL; // minimum  ""            ""
      signed *sumH;
      signed *sumL;
      unsigned int bitWidth;
      const FixedBits & output;

      ColumnCounts(signed _columnH[], signed _columnL[], signed _sumH[], signed _sumL[], unsigned _bitWidth,
          FixedBits& output_) :
          columnH(_columnH), columnL(_columnL), sumH(_sumH), sumL(_sumL), output(output_)
      {
        // setup the low and highs.
        bitWidth = _bitWidth;
        // initialise 'em.
        for (unsigned i = 0; i < bitWidth; i++)
          {
          columnL[i] = 0;
          columnH[i] = i + 1;
          }
      }

      void
      rebuildSums()
      {
        // Initialise sums.
        sumL[0] = columnL[0];
        sumH[0] = columnH[0];
        snapTo(0);

        for (unsigned i = /**/1 /**/; i < bitWidth; i++)
          {
          assert((columnH[i] >= columnL[i]) && (columnL[i] >= 0));
          sumH[i] = columnH[i] + (sumH[i - 1] / 2);
          sumL[i] = columnL[i] + (sumL[i - 1] / 2);
          if (output.isFixed(i))
            snapTo(i);
          }
      }

      void
      print(string message)
      {
        log << message << endl;
        log << " columnL:";
        for (unsigned i = 0; i < bitWidth; i++)
          {
          log << columnL[bitWidth - 1 - i] << " ";
          }
        log << endl;
        log << " columnH:";
        for (unsigned i = 0; i < bitWidth; i++)
          {
          log << columnH[bitWidth - 1 - i] << " ";
          }
        log << endl;
        log << " sumL:   ";

        for (unsigned i = 0; i < bitWidth; i++)
          {
          log << sumL[bitWidth - 1 - i] << " ";
          }
        log << endl;
        log << " sumH:   ";
        for (unsigned i = 0; i < bitWidth; i++)
          {
          log << sumH[bitWidth - 1 - i] << " ";
          }
        log << endl;
      }

      Result
      snapTo(int i)
      {
        Result r = NO_CHANGE;
        if (output.isFixed(i))
          {
          //bool changed = false;
          int expected = output.getValue(i) ? 1 : 0;

          // output is true. So the maximum and minimum can only be even.
          if ((sumH[i] & 1) != expected)
            {
            sumH[i]--;
            r = CHANGED;
            }
          if ((sumL[i] & 1) != expected)
            {
            sumL[i]++;
            r = CHANGED;
            }

          if (((sumH[i] < sumL[i]) || (sumL[i] < 0)))
            return CONFLICT;
          }
        return r;
      }

      // update the sum of a column to the parity of the output for that column. e.g. [0,2] if the answer is 1, goes to [1,1].
      Result
      snapTo()
      {
        Result r = NO_CHANGE;

        // Make sure each column's sum is consistent with the output.
        for (unsigned i = 0; i < bitWidth; i++)
          {
          r = merge(r, snapTo(i));
          }
        return r;
      }

      bool
      inConflict()
      {
        for (unsigned i = 0; i < bitWidth; i++)
          if ((sumL[i] > sumH[i]) || (columnL[i] > columnH[i]))
            return true;
        return false;

      }

      Result
      fixedPoint()
      {
        if (inConflict())
          return CONFLICT;

        bool changed = true;
        bool totalChanged = false;

        while (changed)
          {
          changed = false;

          Result r = snapTo();
          if (r == CHANGED)
            changed = true;
          if (r == CONFLICT)
            return CONFLICT;

          r = propagate();
          if (r == CHANGED)
            changed = true;
          if (r == CONFLICT)
            return CONFLICT;

          if (changed)
            totalChanged = true;
          }

        if (inConflict())
          return CONFLICT;

        assert(propagate() == NO_CHANGE);
        assert(snapTo() == NO_CHANGE);

        if (totalChanged)
          return CHANGED;
        else
          return NO_CHANGE;
      }

      //Assert that all the counts are consistent.
      Result
      propagate()
      {
        bool changed = false;

        int i = 0;

        //
        if (sumL[i] > columnL[i])
          {
          columnL[i] = sumL[i];
          changed = true;
          }
        if (sumL[i] < columnL[i])
          {
          sumL[i] = columnL[i];
          changed = true;
          }
        if (sumH[i] < columnH[i])
          {
          columnH[i] = sumH[i];
          changed = true;
          }
        if (sumH[i] > columnH[i])
          {
          sumH[i] = columnH[i];
          changed = true;
          }

        for (unsigned i = 1; i < bitWidth; i++)
          {
          Interval a(sumL[i], sumH[i]);
          Interval b(columnL[i], columnH[i]);

          int low = sumL[i - 1] / 2; // interval takes references.
          int high = sumH[i - 1] / 2;
          Interval c(low, high);

          if (a.low < b.low + c.low)
            {
            a.low = b.low + c.low;
            changed = true;
            }

          if (a.high > b.high + c.high)
            {
            changed = true;
            a.high = b.high + c.high;
            }

          if (a.low - b.high > c.low)
            {
            int toAssign = ((a.low - b.high) * 2);
            assert(toAssign > sumL[i - 1]);
            sumL[i - 1] = toAssign;
            changed = true;
            }

          if (a.high - b.low < c.high)
            {
            int toAssign = ((a.high - b.low) * 2) + 1;
            assert(toAssign < sumH[i - 1]);
            sumH[i - 1] = toAssign;
            changed = true;
            }

          if (a.low - c.high > b.low)
            {
            b.low = a.low - c.high;
            changed = true;
            }

          if (a.high - c.low < b.high)
            {
            b.high = a.high - c.low;
            changed = true;
            }

          }
        if (changed)
          return CHANGED;
        else
          return NO_CHANGE;
      }
    };
  }
}

#endif /* COLUMNCOUNTS_H_ */
