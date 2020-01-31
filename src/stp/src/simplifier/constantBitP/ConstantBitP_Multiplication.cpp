#include "ConstantBitP_TransferFunctions.h"
#include "ConstantBitP_Utility.h"
#include <set>
#include <stdexcept>
#include "../../AST/AST.h"
#include "../../simplifier/simplifier.h"
#include "MultiplicationStats.h"
#include "multiplication/ColumnCounts.h"
#include "multiplication/ColumnStats.h"
// Multiply.

namespace simplifier
{
  namespace constantBitP
  {
    using std::endl;
    using std::pair;
    using std::set;

    const bool debug_multiply = false;
    std::ostream& log = std::cerr;

#if 0
// The maximum size of the carry into a column for MULTIPLICATION
    int
    maximumCarryInForMultiplication(int column)
      {
      int result = 0;
      int currIndex = 0;

      while (currIndex < column)
        {
        currIndex++;
        result = (result + currIndex) / 2;
        }

      return result;
      }
#endif

    Result
    fixIfCanForMultiplication(vector<FixedBits*>& children, const int index, const int aspirationalSum)
    {
      assert(index >=0);
      assert(index < children[0]->getWidth());

      FixedBits& x = *children[0];
      FixedBits& y = *children[1];

      ColumnStats cs(x, y, index);

      int columnUnfixed = cs.columnUnfixed; // both unfixed.
      int columnOneFixed = cs.columnOneFixed; // one of the values is fixed to one.
      int columnOnes = cs.columnOnes; // both are ones.

      Result result = NO_CHANGE;

      // only one of the conditionals can run.
      bool run = false;

      // We need every value that is unfixed to be set to one.
      if (aspirationalSum == columnOnes + columnOneFixed + columnUnfixed && ((columnOneFixed + columnUnfixed) > 0))
        {
        for (unsigned i = 0; i <= (unsigned) index; i++)
          {
          // If y is unfixed, and it's not anded with zero.
          if (!y.isFixed(i) && !(x.isFixed(index - i) && !x.getValue(index - i)))
            {
            y.setFixed(i, true);
            y.setValue(i, true);
            result = CHANGED;
            }

          if (!x.isFixed(index - i) && !(y.isFixed(i) && !y.getValue(i)))
            {
            x.setFixed(index - i, true);
            x.setValue(index - i, true);
            result = CHANGED;
            }
          }assert(result == CHANGED);
        run = true;
        }

      // We have all the ones that we need already. (thanks). Set everything we can to zero.
      if (aspirationalSum == columnOnes && (columnUnfixed > 0 || columnOneFixed > 0))
        {
        assert(!run);
        for (unsigned i = 0; i <= (unsigned) index; i++)
          {
          if (!y.isFixed(i) && x.isFixed(index - i) && x.getValue(index - i)) // one fixed.

            {
            y.setFixed(i, true);
            y.setValue(i, false);
            result = CHANGED;
            }

          if (!x.isFixed(index - i) && y.isFixed(i) && y.getValue(i)) // one fixed other way.
            {
            x.setFixed(index - i, true);
            x.setValue(index - i, false);
            result = CHANGED;
            }
          }
        }
      if (debug_multiply && result == CONFLICT)
        log << "CONFLICT" << endl;

      return result;
    }

// Uses the zeroes / ones present adjust the column counts.
    Result
    adjustColumns(const FixedBits& x, const FixedBits& y, int* columnL, int * columnH)
    {
      const unsigned bitWidth = x.getWidth();

      bool yFixedFalse[bitWidth];
      bool xFixedFalse[bitWidth];

      for (unsigned i = 0; i < bitWidth; i++)
        {
        yFixedFalse[i] = y.isFixed(i) && !y.getValue(i);
        xFixedFalse[i] = x.isFixed(i) && !x.getValue(i);
        }

      for (unsigned i = 0; i < bitWidth; i++)
        {
        // decrease using zeroes.
        if (yFixedFalse[i])
          {
          for (unsigned j = i; j < bitWidth; j++)
            {
            columnH[j]--;
            }
          }

        if (xFixedFalse[i])
          {
          for (unsigned j = i; j < bitWidth; j++)
            {
            // if the row hasn't already been zeroed out.
            if (!yFixedFalse[j - i])
              columnH[j]--;
            }
          }

        // check if there are any pairs of ones.
        if (x.isFixed(i) && x.getValue(i))
          for (unsigned j = 0; j < (bitWidth - i); j++)
            {
            assert(i + j < bitWidth);
            if (y.isFixed(j) && y.getValue(j))
              {
              // a pair of ones. Increase the lower bound.
              columnL[i + j]++;
              }
            }
        }
      return NO_CHANGE;
    }

    Result
    setToZero(FixedBits& y, int from, int to)
    {
      Result r = NO_CHANGE;
      assert(from<=to);
      assert(from>= 0);
      assert(to <= y.getWidth());

      /***NB < to ***/
      for (int i = from; i < to; i++)
        {
        if (y[i] == '*')
          {
          y.setFixed(i, true);
          y.setValue(i, false);
          r = CHANGED;
          }
        else if (y[i] == '1')
          return CONFLICT;
        }
      return r;
    }

// Finds the leading one in each of the two inputs.
// If this position is i & j, then in the output
// there can be no ones higher than i+j+1.
    Result
    useLeadingZeroesToFix_OLD(FixedBits& x, FixedBits&y, FixedBits& output)
    {
      // Count the leading zeroes on x & y.
      // Output should have about that many..
      int xTop = x.topmostPossibleLeadingOne();
      int yTop = y.topmostPossibleLeadingOne();

      int maxOutputOneFromInputs = xTop + yTop + 1;

      for (int i = output.getWidth() - 1; i > maxOutputOneFromInputs; i--)
        if (!output.isFixed(i))
          {
          output.setFixed(i, true);
          output.setValue(i, false);
          }
        else
          {
          if (output.getValue(i))
            return CONFLICT;
          }

      return NOT_IMPLEMENTED;
    }

    Result
    useLeadingZeroesToFix(FixedBits& x, FixedBits&y, FixedBits& output)
    {
      // To check that the new implementation subsumes the old.
#ifndef NDEBUG
      FixedBits x_p = x;
      FixedBits y_p = y;
      FixedBits o_p = output;
      useLeadingZeroesToFix_OLD(x_p, y_p, o_p);
#endif

      const int bitWidth = x.getWidth();
      CBV x_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);
      CBV y_c = CONSTANTBV::BitVector_Create(2 * bitWidth, true);

      for (int i = 0; i < bitWidth; i++)
        {
        if (x[i] == '1' || x[i] == '*')
          CONSTANTBV::BitVector_Bit_On(x_c, i);

        if (y[i] == '1' || y[i] == '*')
          CONSTANTBV::BitVector_Bit_On(y_c, i);
        }

      BEEV::CBV result = CONSTANTBV::BitVector_Create(2 * bitWidth + 1, true);
      CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(result, x_c, y_c);
      assert(ec == CONSTANTBV::ErrCode_Ok);

      for (int j = (2 * bitWidth) - 1; j >= 0; j--)
        {
        if (CONSTANTBV::BitVector_bit_test(result, j))
          break;
        if (j < bitWidth)
          {
          if (!output.isFixed(j))
            {
            output.setFixed(j, true);
            output.setValue(j, false);
            }
          else
            {
            if (output.getValue(j))
              return CONFLICT;
            }

          }
        }

#ifndef NDEBUG
      // Assert the new implementation fixes more than the old.
      assert(FixedBits::in(x,x_p ));
      assert(FixedBits::in(y,y_p ));
      assert(FixedBits::in(output, o_p));
#endif

      CONSTANTBV::BitVector_Destroy(x_c);
      CONSTANTBV::BitVector_Destroy(y_c);
      CONSTANTBV::BitVector_Destroy(result);

      return NOT_IMPLEMENTED;
    }

    Result
    trailingOneReasoning_OLD(FixedBits& x, FixedBits&y, FixedBits& output);


    // Remove from x any trailing "boths", that don't have support in y and output.
        Result
        trailingOneReasoning(FixedBits& x, FixedBits&y, FixedBits& output)
        {
          Result r = NO_CHANGE;

          const int bitwidth = output.getWidth();

          const int y_min = y.minimum_trailingOne();
          const int y_max = y.maximum_trailingOne();

          const int output_max = output.maximum_trailingOne();

          for (int i = 0; i < bitwidth; i++)
            {
            if (x[i] == '0')
              continue;

            if (x[i] == '1')
              break;

            for (int j = y_min; j <= std::min(y_max, output_max); j++)
              {
                if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
                  return r;
              }

              x.setFixed(i, true);
              x.setValue(i, false);
              r = CHANGED;
            }

          assert(trailingOneReasoning_OLD(x,y,output) == NO_CHANGE);
          return r;
        }

// Remove from x any trailing "boths", that don't have support in y and output.
    Result
    trailingOneReasoning_OLD(FixedBits& x, FixedBits&y, FixedBits& output)
    {
      Result r = NO_CHANGE;

      const int bitwidth = output.getWidth();

      const int x_min = x.minimum_trailingOne();
      const int x_max = x.maximum_trailingOne();

      const int y_min = y.minimum_trailingOne();
      const int y_max = y.maximum_trailingOne();

      int output_max = output.maximum_trailingOne();

      bool done = false;
      for (int i = x_min; i <= std::min(x_max, bitwidth - 1); i++)
        {
        if (x[i] == '1')
          break;

        if (x[i] == '0')
          continue;

        assert(!done);
        for (int j = y_min; j <= std::min(y_max, output_max); j++)
          {
          if (j + i >= bitwidth || (y[j] != '0' && output[i + j] != '0'))
            {
            done = true;
            break;
            }
          }
        if (!done)
          {
          x.setFixed(i, true);
          x.setValue(i, false);
          r = CHANGED;
          }
        else
          break;
        }
      return r;
    }

// if x has n trailing zeroes, and y has m trailing zeroes, then the output has n+m trailing zeroes.
// if the output has n trailing zeroes and x has p trailing zeroes, then y has n-p trailing zeroes.
    Result
    useTrailingZeroesToFix(FixedBits& x, FixedBits&y, FixedBits& output)
    {
      const int bitwidth = output.getWidth();

      Result r0 = trailingOneReasoning(x, y, output);
      Result r1 = trailingOneReasoning(y, x, output);

      //Calculate the minimum number of trailing zeroes in the operands,
      //the result has a >= number.
      int min = x.minimum_numberOfTrailingZeroes() + y.minimum_numberOfTrailingZeroes();
      min = std::min(min, bitwidth);

      Result r2 = setToZero(output, 0, min);
      if (r2 == CONFLICT)
        return CONFLICT;

      if (r0 == CHANGED || r1 == CHANGED || r2 == CHANGED)
        return CHANGED;

      return NO_CHANGE;
    }

    Result
    useInversesToSolve(FixedBits& x, FixedBits&y, FixedBits& output, BEEV::STPMgr* bm)
    {
      // Position of the first unfixed value +1.
      int xBottom = x.leastUnfixed();
      int yBottom = y.leastUnfixed();
      int outputBottom = output.leastUnfixed();

      int invertCount = std::min(std::max(xBottom, yBottom), outputBottom);

      if (invertCount == 0)
        return NO_CHANGE;

      FixedBits* toInvert;
      FixedBits* toSet;

      if (xBottom > yBottom)
        {
        toInvert = &x;
        toSet = &y;
        }
      else
        {
        toInvert = &y;
        toSet = &x;
        }

      invertCount--; // position of the least fixed.

      const unsigned int width = invertCount + 1;
      BEEV::CBV toInvertCBV = toInvert->GetBVConst(invertCount, 0);

      //cerr << "value to invert:" << *toInvertCBV << " ";

      Result status = NOT_IMPLEMENTED;

      if (CONSTANTBV::BitVector_bit_test(toInvertCBV, 0))
        {

        if (debug_multiply)
          cerr << "Value to Invert:" << *toInvertCBV << endl;

        BEEV::Simplifier simplifier(bm);
        BEEV::CBV inverse = simplifier.MultiplicativeInverse(bm->CreateBVConst(toInvertCBV, width)).GetBVConst();
        BEEV::CBV toMultiplyBy = output.GetBVConst(invertCount, 0);

        BEEV::CBV toSetEqualTo = CONSTANTBV::BitVector_Create(2 * (width), true);

        CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(toSetEqualTo, inverse, toMultiplyBy);
        if (ec != CONSTANTBV::ErrCode_Ok)
          {
          assert(false);
          throw 2314231;
          }

        if (false && debug_multiply)
          {
          cerr << x << "*" << y << "=" << output << endl;
          cerr << "Invert bit count" << invertCount << endl;
          cerr << "To set" << *toSet;
          cerr << "To set equal to:" << *toSetEqualTo << endl;
          }

        // Write in the value.
        for (int i = 0; i <= invertCount; i++)
          {
          bool expected = CONSTANTBV::BitVector_bit_test(toSetEqualTo, i);

          if (toSet->isFixed(i) && (toSet->getValue(i) ^ expected))
            {
            status = CONFLICT;
            }
          else if (!toSet->isFixed(i))
            {
            toSet->setFixed(i, true);
            toSet->setValue(i, expected);
            }
          }

        // Don't delete the "inverse" because it's reference counted by the ASTNode.

        CONSTANTBV::BitVector_Destroy(toSetEqualTo);
        CONSTANTBV::BitVector_Destroy(toMultiplyBy);

        //cerr << "result" << *toSet;
        }
      else
        CONSTANTBV::BitVector_Destroy(toInvertCBV);

      //cerr << endl;
      return status;
    }

// Use trailing fixed to fix.
// Create two constants and multiply them out fixing the result.
    Result
    useTrailingFixedToFix(FixedBits& x, FixedBits&y, FixedBits& output)
    {
      int xBottom = x.leastUnfixed();
      int yBottom = y.leastUnfixed();

      int minV = std::min(xBottom, yBottom);

      if (minV == 0)
        return NO_CHANGE; // nothing determined.

      // It gives the position of the first non-fixed. We want the last fixed.
      minV--;

      // The multiply doesn't like to overflow. So we widen the output.
      BEEV::CBV xCBV = x.GetBVConst(minV, 0);
      BEEV::CBV yCBV = y.GetBVConst(minV, 0);
      BEEV::CBV result = CONSTANTBV::BitVector_Create(2 * (minV + 1), true);

      CONSTANTBV::ErrCode ec = CONSTANTBV::BitVector_Multiply(result, xCBV, yCBV);
      if (ec != CONSTANTBV::ErrCode_Ok)
        {
        assert(false);
        throw 2314231;
        }

      Result status = NOT_IMPLEMENTED;
      for (int i = 0; i <= minV; i++)
        {
        bool expected = CONSTANTBV::BitVector_bit_test(result, i);

        if (output.isFixed(i) && (output.getValue(i) ^ expected))
          status = CONFLICT;
        else if (!output.isFixed(i))
          {
          output.setFixed(i, true);
          output.setValue(i, expected);
          }
        }

      CONSTANTBV::BitVector_Destroy(xCBV);
      CONSTANTBV::BitVector_Destroy(yCBV);
      CONSTANTBV::BitVector_Destroy(result);

      return status;
    }

    void
    printColumns(signed *sumL, signed * sumH, int bitWidth)
    {
      for (int i = 0; i < bitWidth; i++)
        {
        log << sumL[bitWidth - 1 - i] << " ";
        }
      log << endl;
      for (int i = 0; i < bitWidth; i++)
        {
        log << sumH[bitWidth - 1 - i] << " ";
        }
      log << endl;
    }

    Result
    bvMultiplyBothWays(vector<FixedBits*>& children, FixedBits& output, BEEV::STPMgr* bm, MultiplicationStats* ms)
    {
      FixedBits & x = *children[0];
      FixedBits & y = *children[1];

      assert(x.getWidth() == y.getWidth());
      assert(x.getWidth() == output.getWidth());

      const unsigned bitWidth = x.getWidth();

      if (debug_multiply)
        cerr << "======================" << endl;

      if (debug_multiply)
        {
        cerr << "Initial Fixing";
        cerr << x << "*";
        cerr << y << "=";
        cerr << output << endl;
        }

      Result r = useTrailingZeroesToFix(x, y, output);
      if (CONFLICT == r)
        return r;

      bool changed = true;
      while (changed)
        {
        changed = false;
        signed columnH[bitWidth]; // maximum number of true partial products.
        signed columnL[bitWidth]; // minimum  ""            ""
        signed sumH[bitWidth];
        signed sumL[bitWidth];

        ColumnCounts cc(columnH, columnL, sumH, sumL, bitWidth, output);

        // Use the number of zeroes and ones in a column to update the possible counts.
        adjustColumns(x, y, columnL, columnH);

        cc.rebuildSums();
        Result r = cc.fixedPoint();

        if (r == CONFLICT)
          return CONFLICT;

        r = NO_CHANGE;

        // If any of the sums have a cardinality of 1. Set the result.
        for (unsigned column = 0; column < bitWidth; column++)
          {
          if (cc.sumL[column] == cc.sumH[column])
            {
            //(1) If the output has a known value. Set the output.
            bool newValue = !(sumH[column] % 2 == 0);
            if (!output.isFixed(column))
              {
              output.setFixed(column, true);
              output.setValue(column, newValue);
              r = CHANGED;
              }
            else if (output.getValue(column) != newValue)
              return CONFLICT;
            }
          }

        if (CHANGED == r)
          changed = true;

        for (unsigned column = 0; column < bitWidth; column++)
          {
          if (cc.columnL[column] == cc.columnH[column])
            {
            //(2) Knowledge of the sum may fix the operands.
            Result tempResult = fixIfCanForMultiplication(children, column, cc.columnH[column]);

            if (CONFLICT == tempResult)
              return CONFLICT;

            if (CHANGED == tempResult)
              r = CHANGED;
            }
          }

        if (debug_multiply)
          {
          cerr << "At end";
          cerr << "x:" << x << endl;
          cerr << "y:" << y << endl;
          cerr << "output:" << output << endl;
          }

        assert(CONFLICT != r);

        if (CHANGED == r)
          changed = true;

        if (ms != NULL)
          {
          *ms = MultiplicationStats(bitWidth, cc.columnL, cc.columnH, cc.sumL, cc.sumH);
          ms->x = *children[0];
          ms->y = *children[1];
          ms->r = output;
          }

        if (changed)
          {
          useTrailingZeroesToFix(x, y, output);
          //  if (r == NO_CHANGE)
          //    changed= false;
          }
        }

      if (children[0]->isTotallyFixed() && children[1]->isTotallyFixed())
        {
        assert(output.isTotallyFixed());
        }

// The below assertions are for performance only. It's not maximally precise anyway!!!

#ifndef NDEBUG
      if (r != CONFLICT)
        {
        FixedBits x_c(x), y_c(y), o_c(output);

        // These are subsumed by the consistency over the columns..
        useTrailingFixedToFix(x_c, y_c, o_c);
        useLeadingZeroesToFix(x_c, y_c, o_c);
        useInversesToSolve(x_c, y_c, o_c, bm);

        // This one should have been called to fixed point!
        useTrailingZeroesToFix(x_c, y_c, o_c);

        if (!FixedBits::equals(x_c, x) || !FixedBits::equals(y_c, y) || !FixedBits::equals(o_c, output))
          {
          cerr << x << y << output << endl;
          cerr << x_c << y_c << o_c << endl;
          assert(false);
          }
        }
#endif

      return NOT_IMPLEMENTED;
    }
  }
}
