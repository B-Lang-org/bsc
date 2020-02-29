#ifndef FIXEDBITS_H_
#define FIXEDBITS_H_

#include <vector>
#include <iostream>
#include <cassert>

class MTRand;

namespace BEEV
{
  class ASTNode;
  typedef unsigned int * CBV;
  void FatalError(const char * str);
}

namespace simplifier
{
  namespace constantBitP
  {

    // Gives the file and line number as a string.
#define CONSTANTBITP_UTILITY_STR(s) #s
#define CONSTANTBITP_UTILITY_XSTR(s) CONSTANTBITP_UTILITY_STR(s)
#define LOCATION __FILE__ ":"  CONSTANTBITP_UTILITY_XSTR(__LINE__) ": "

    static int staticUniqueId = 1;

    // Bits can be fixed, or unfixed. Fixed bits are fixed to either zero or one.
    class FixedBits
    {
    private:
      bool* fixed;
      bool* values;
      int width;
      bool representsBoolean;

      void
      init(const FixedBits& copy);
      int uniqueId;

      bool
      unsignedHolds_new(unsigned val);
      bool
      unsignedHolds_old(unsigned val);


    public:
      FixedBits(int n, bool isBoolean);

      FixedBits(const FixedBits& copy)
      {
        assert(this != &copy);
        init(copy);
        uniqueId = staticUniqueId++;
      }

      bool
      isBoolean() const
      {
        return representsBoolean;
      }

      ~FixedBits()
      {
        delete[] fixed;
        delete[] values;
      }

      bool
      operator<=(const FixedBits& copy) const
      {
        return uniqueId <= copy.uniqueId;
      }

      const char
      operator[] (const int n) const
      {
        assert(n >=0 && n <width);
        if (!isFixed(n))
            return '*';
        else if (getValue(n))
            return '1';
        else
            return '0';
      }

      // Equality when I was a java programmer sorry!~.
      bool
      operator==(const FixedBits& other) const
      {
        return this == &(other);
      }

      FixedBits&
      operator=(const FixedBits& copy)
      {
        if (this == &copy)
          return *this;
        delete[] fixed;
        delete[] values;
        init(copy);
        return *this;
      }

      //All values are fixed to false.
      void
      fixToZero();

      int
      getWidth() const
      {
        return width;
      }

      // the value contained in the fixed thingy.
      int
      getUnsignedValue() const;

      // True if all bits are fixed (irrespective of what value they are fixed to).
      bool
      isTotallyFixed() const;

      // set value of bit "n" to the value.
      void
      setValue(int n, bool value)
      {
        assert(((char)value) == 0 || (char)value ==1 );
        assert(n >=0 && n <width && fixed[n]);
        values[n] = value;
      }

      bool
      getValue(int n) const
      {
        assert(n >=0 && n <width && fixed[n]);
        return values[n];
      }

      //returns -1 if it's zero.
      int
      topmostPossibleLeadingOne()
      {
        int i = 0;
        for (i = getWidth() - 1; i >= 0; i--)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      int
      minimum_trailingOne()
      {
        int i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      int
      maximum_trailingOne()
      {
        int i = 0;
        for (; i < getWidth(); i++)
          {
            if (isFixed(i) && getValue(i))
              break;
          }
        return i;
      }



      int
      minimum_numberOfTrailingZeroes()
      {
        int i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i) || getValue(i))
              break;
          }
        return i;
      }

      int
      maximum_numberOfTrailingZeroes()
      {
        int i = 0;
        for (; i < getWidth(); i++)
          {
            if (isFixed(i) && getValue(i))
              break;
          }
        return i;
      }

      //Returns the position of the first non-fixed value.
      int
      leastUnfixed() const
      {
        int i = 0;
        for (; i < getWidth(); i++)
          {
            if (!isFixed(i))
              break;
          }
        return i;
      }

      int
      mostUnfixed() const
      {
        int i = getWidth()-1;
        for (; i >=0; i--)
          {
            if (!isFixed(i))
              break;
          }
        return i;
      }

      // is this bit fixed to zero?
      bool
      isFixedToZero(int n) const
      {
        return isFixed(n) && !getValue(n);
      }

      // is this bit fixed to one?
      bool
      isFixedToOne(int n) const
      {
        return isFixed(n) && getValue(n);
      }

      // is this bit fixed to either zero or one?
      bool
      isFixed(int n) const
      {
        assert(n >=0 && n <width);
        return fixed[n];
      }

      // set bit n to either fixed or unfixed.
      void
      setFixed(int n, bool value)
      {
        assert(((char)value) == 0 || (char)value ==1 );
        assert(n >=0 && n <width);
        fixed[n] = value;
      }


      // Whether the set of values contains this one.
      bool
      unsignedHolds(unsigned val);

      void
      replaceWithContents(const FixedBits& a)
      {
        assert(getWidth() >= a.getWidth());

        for (int i = 0; i < a.getWidth(); i++)
          {
            if (a.isFixed(i))
              {
                setFixed(i, true);
                setValue(i, a.getValue(i));
              }
            else
              {
                setFixed(i, false);
              }
          }
      }


      void
      copyIn(const FixedBits& a)
      {
        int to = std::min(getWidth(), a.getWidth());
        for (int i = 0; i < to; i++)
          {
            assert(!isFixed(i));
            if (a.isFixed(i))
              {
                setFixed(i, true);
                setValue(i, a.getValue(i));
              }
          }
      }

      //todo merger with unsignedHolds()
      bool
      containsZero() const
      {
        for (int i = 0; i < getWidth(); i++)
          if (isFixed(i) && getValue(i))
            return false;
        return true;
      }

      int
      countFixed() const
      {
        int result = 0;
        for (unsigned i = 0; i < (unsigned) width; i++)
          if (isFixed(i))
            result++;
        return result;
      }

      // Result needs to be explicitly deleted.
      BEEV::CBV
      GetBVConst() const;

      // Result needs to be explicitly deleted.
      BEEV::CBV
      GetBVConst(int to, int from) const;

      void
      getUnsignedMinMax(unsigned &minShift, unsigned &maxShift) const;

      void
      mergeIn(const FixedBits& a)
      {
        assert(a.getWidth() == getWidth());
        for (int i= 0; i < width;i++)
          {
          if (a.isFixed(i) && !isFixed(i))
            {
            setFixed(i,true);
            setValue(i,a.getValue(i));
            }
          }
      }


      static FixedBits
      meet(const FixedBits& a, const FixedBits& b);

      void
      join(const FixedBits& a);

      void
      join(unsigned int a);


      static FixedBits
      createRandom(const int length, const int probabilityOfSetting,
          MTRand& rand);

      void
      fromUnsigned(unsigned val);

      static FixedBits
      fromUnsignedInt(int width, unsigned val);

      static FixedBits
      concreteToAbstract(const BEEV::ASTNode& n);

      static bool
      equals(const FixedBits& a, const FixedBits& b);

      static bool
      equals(const FixedBits& a, const FixedBits& b, const int upTo);

      static bool
      updateOK(const FixedBits& o, const FixedBits & n);

      static bool
      updateOK(const FixedBits& o, const FixedBits &n, const int upTo);

      static bool
      in(const FixedBits& a, const FixedBits& b);

    };

    std::ostream&
    operator<<(std::ostream& output, const FixedBits& h);

  }
}
#endif /*FIXED_H_*/
