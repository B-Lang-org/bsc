#include "../../AST/AST.h"
#include "FixedBits.h"
#include "MersenneTwister.h"


#include "ConstantBitP_Utility.h"

// To reduce the memory I tried using the constantbv stuff. But because it is not
// inlined it took about twice as long per propagation as does using a boolean array.
// Other options to reduce memory usage are: vector<bool>, dynamic_bitset, or bitMagic.


namespace simplifier
{
  namespace constantBitP
  {

    std::ostream&
    operator<<(std::ostream& output, const FixedBits& h)
    {
      output << "<";
      for (int i = h.getWidth() - 1; i >= 0; i--)
        {
          if (h.isFixed(i))
            output << h.getValue(i);
          else
            output << "-";
        }

      output << ">";

      return output;
    }

    void
    FixedBits::fixToZero()
    {
      for (int i = 0; i < getWidth(); i++)
        {
          setFixed(i, true);
          setValue(i, false);
        }
    }

    BEEV::CBV
    FixedBits::GetBVConst() const
    {
      assert(isTotallyFixed());

      BEEV::CBV result = CONSTANTBV::BitVector_Create(width, true);

      for (int i = 0; i < width; i++)
        {
          if (values[i])
            CONSTANTBV::BitVector_Bit_On(result, i);
        }

      return result;
    }

    //inclusive
    BEEV::CBV
    FixedBits::GetBVConst(int to, int from) const
    {
      assert(to>=from);
      assert(from >=0);
      int resultWidth = to - from + 1;

      BEEV::CBV result = CONSTANTBV::BitVector_Create(resultWidth, true);

      for (int i = from; i <= to; i++)
        {
          if (getValue(i))
            CONSTANTBV::BitVector_Bit_On(result, i - from);
        }

      return result;
    }

    void
    FixedBits::init(const FixedBits& copy)
    {
      width = copy.width;
      fixed = new bool[width];
      values = new bool[width];
      representsBoolean = copy.representsBoolean;

      memcpy(fixed, copy.fixed, width * sizeof(bool));
      memcpy(values, copy.values, width * sizeof(bool));
    }

    bool
    FixedBits::isTotallyFixed() const
    {
      for (int i = 0; i < width; i++)
        {
          if (!fixed[i])
            return false;
        }

      return true;
    }

    FixedBits::FixedBits(int n, bool isbool)
    {
      assert(n > 0);

      fixed = new bool[n];
      values = new bool[n];
      width = n;

      for (int i = 0; i < width; i++)
        {
          fixed[i] = false; // I don't know if there's a default value??
          values[i] = false; // stops it printing out junk.
        }

      representsBoolean = isbool;
      if (isbool)
        assert(1 == width);

      uniqueId = staticUniqueId++;
    }

    // There is no way to represent bottom. So we assume a and b are already at least
    // one step up the lattice.
    FixedBits
    FixedBits::meet(const FixedBits& a, const FixedBits& b)
    {
      assert(a.getWidth() == b.getWidth());
      assert(a.isBoolean() == b.isBoolean());

      FixedBits result(a.getWidth(), a.isBoolean());

      for (int i = 0; i < a.getWidth(); i++)
        {
          if (a.isFixed(i) != b.isFixed(i))
            {
              result.setFixed(i, false);
            }
          else if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i)
              != b.getValue(i)))
            {
              result.setFixed(i, false);
            }
          else if (a.isFixed(i) && b.isFixed(i))
            { // fixed to the same value.
              result.setFixed(i, true);
              result.setValue(i, a.getValue(i));
            }
        }
      return result;
    }



    void
    FixedBits::join(const FixedBits& a)
    {
      assert(a.getWidth() == getWidth());
      assert(a.isBoolean() == isBoolean());

      for (int i = 0; i < a.getWidth(); i++)
        {
          if (a.isFixed(i) && isFixed(i) && (a.getValue(i) == getValue(i)))
            {
              // nothind.
            }
          else
            {
              setFixed(i,false);
            }
        }
    }

    void
    FixedBits::join(unsigned int a)
    {
      for (int i = 0; i < getWidth(); i++)
        {
          if (isFixed(i))
            {
                if (
                    (((a >> i) & 1) ==1)
                  &&
                    !getValue(i)
                   )
                  setFixed(i,false);
                else if ((((a >> i) & 1) ==0) && getValue(i))
                  setFixed(i,false);
            }
        }
    }

    bool
    FixedBits::unsignedHolds(unsigned val)
    {
      bool r = unsignedHolds_new(val);
      //assert (unsignedHolds_old(val) == r);
      return r;
    }

    // Whether the set of values contains this one. Much faster than the _old version.
    bool
    FixedBits::unsignedHolds_new(unsigned val)
    {
      const int initial_width = std::min((int)width, (int)sizeof(unsigned) * 8);

      for (int i = 0; i < initial_width; i++)
        {
          char v = (*this)[i];
          if ('*'== v)
            {} // ok
          else if ((v == '1') != ((val & 1) != 0))
            return false;
          val = val >> 1;
        }

      // If the unsigned representation is bigger, false if not zero.
      if ((int) sizeof(unsigned) * 8 > width && (val !=0))
         return false;

      for (int i = (int) sizeof(unsigned) * 8; i < width; i++)
        if (isFixed(i) && getValue(i))
          return false;

      return true;
    }

    bool
    FixedBits::unsignedHolds_old(unsigned val)
    {
      const unsigned maxWidth = std::max((int) sizeof(unsigned) * 8, width);
      for (unsigned i = 0; i < maxWidth; i++)
        {
        if (i < (unsigned) width && i < sizeof(unsigned) * 8)
          {
          if (isFixed(i) && (getValue(i) != (((val & (1 << i))) != 0)))
            return false;
          }
        else if (i < (unsigned) width)
          {
          if (isFixed(i) && getValue(i))
            return false;
          }
        else // The unsigned value is bigger than the bitwidth of this.
          {
          if (val & (1 << i))
            return false;
          }
        }
      return true;
    }

    // Getting a new random number is expensive. Not sure why.
    FixedBits FixedBits::createRandom(const int length, const int probabilityOfSetting, MTRand& trand)
      {
        assert( 0 <= probabilityOfSetting);
        assert( 100 >= probabilityOfSetting);

        FixedBits result(length, false);

        // I'm not sure if the random number generator is generating just 32 bit numbers??
        int i = 0;
        int randomV = trand.randInt();

        int pool = 32;

        while (i < length)
          {
            if (pool < 8)
              {
                randomV = trand.randInt();
                pool = 32;
              }

            int val = (randomV & 127);
            randomV >>= 7;
            pool = pool - 7;

            if (val >= 100)
            continue;

            if (val < probabilityOfSetting)
              {
                switch (randomV & 1)
                  {
                    case 0:
                    result.setFixed(i, true);
                    result.setValue(i, false);
                    break;
                    case 1:
                    result.setFixed(i, true);
                    result.setValue(i, true);
                    break;
                    default:
                    BEEV::FatalError(LOCATION "never.");

                  }
                randomV >>= 1;
              }
            i++;

          }
        return result;
      }

    // In the world of static analysis this is ALPHA.
    FixedBits
    FixedBits::concreteToAbstract(const BEEV::ASTNode& n)
    {
      //cout << n;

      int bitWidth;
      if (BEEV::BITVECTOR_TYPE == n.GetType())
        bitWidth = n.GetValueWidth();
      else
        bitWidth = 1;

      FixedBits output(bitWidth, BEEV::BOOLEAN_TYPE == n.GetType());

      if (BEEV::BITVECTOR_TYPE == n.GetType())
        {
          // loop through testing each of the bits.
          BEEV::CBV cbv = n.GetBVConst();

          for (int j = 0; j < bitWidth; j++)
            {
              output.setFixed(j, true);
              output.setValue(j, CONSTANTBV::BitVector_bit_test(cbv, j));
            }
        }
      else
        {
          if (n.GetKind() == BEEV::TRUE)
            {
              output.setFixed(0, true);
              output.setValue(0, true);
            }
          else if (n.GetKind() == BEEV::FALSE)
            {
              output.setFixed(0, true);
              output.setValue(0, false);
            }
          else
            BEEV::FatalError("Unexpected", n);
        }
      return output;
    }

    FixedBits
    FixedBits::fromUnsignedInt(int width, unsigned val)
    {
      FixedBits output(width, false);

      const unsigned maxWidth = std::max((int) sizeof(unsigned) * 8, width);
      for (unsigned i = 0; i < maxWidth; i++)
        {
          if (i < (unsigned) width && i < sizeof(unsigned) * 8)
            {
              output.setFixed(i, true);
              output.setValue(i, (val & (1 << i)));
            }
          else if (i < (unsigned) width)
            {
              output.setFixed(i, true);
              output.setValue(i, false);

            }
          else // The unsigned value is bigger than the bitwidth of this.
            { // so it can't be represented.
              if (val & (1 << i))
                {
                  BEEV::FatalError(LOCATION "Cant be represented.");
                }
            }
        }
      return output;
    }


    void
    FixedBits::fromUnsigned(unsigned val)
    {
      for (unsigned i = 0; i < width; i++)
        {
          if (i < (unsigned) width && i < sizeof(unsigned) * 8)
            {
              setFixed(i, true);
              setValue(i, (val & (1 << i)));
            }
          else if (i < (unsigned) width)
            {
              setFixed(i, true);
              setValue(i, false);
            }
          else // The unsigned value is bigger than the bitwidth of this.
            { // so it can't be represented.
              if (val & (1 << i))
                {
                  BEEV::FatalError(LOCATION "Cant be represented.");
                }
            }
        }
    }

    int
    FixedBits::getUnsignedValue() const
    {
      assert(isTotallyFixed());
      assert(getWidth() <= 32);
      int result = 0;

      for (int i = 0; i < width; i++)
        {
          if (getValue(i))
            result += (1 << i);
        }
      return result;
    }

    bool
    FixedBits::updateOK(const FixedBits& o, const FixedBits &n, const int upTo)
    {
      assert (n.getWidth() >= upTo);
      assert (o.getWidth() >= upTo);

      for (int i = 0; i < upTo; i++)
        {
          if (n.isFixed(i) && o.isFixed(i))
            {
              if (n.getValue(i) != o.getValue(i))
                {
                  return false;
                }
            }
          else if (o.isFixed(i) && !n.isFixed(i))
            {
              return false;
            }
        }
      return true;
    }

    // If the oldBits can't become the new bits. While respecting the lattice rules. That's bad.
    // For example. A transfer function shouldn't unfix bits. Or chance the fixed bits value.
    bool
    FixedBits::updateOK(const FixedBits& o, const FixedBits &n)
    {
      if (n.getWidth() != o.getWidth())
        return false;

      for (int i = 0; i < n.getWidth(); i++)
        {
          if (n.isFixed(i) && o.isFixed(i))
            {
              if (n.getValue(i) != o.getValue(i))
                {
                  return false;
                }
            }
          else if (o.isFixed(i) && !n.isFixed(i))
            {
              return false;
            }
        }
      return true;
    }

    // a is "IN" b.
    bool
    FixedBits::in(const FixedBits& a, const FixedBits& b)
    {
      assert(a.getWidth() == b.getWidth());

      for (int i = 0; i < a.getWidth(); i++)
        {
          if (a.isFixed(i) && b.isFixed(i) && (a.getValue(i) != b.getValue(i)))
            {
              return false;
            }
          if (!a.isFixed(i) && b.isFixed(i))
            return false;
        }
      return true;
    }

    // Gets the minimum and maximum unsigned values that are held in the current
    // set. It saturates to UINT_MAX.
    void
    FixedBits::getUnsignedMinMax(unsigned &minShift, unsigned &maxShift) const
    {
      const int bitWidth = this->getWidth();
      int unsignedBW = sizeof(unsigned)*8;

      minShift = 0;
      maxShift = 0;

      bool bigMax = false;
      bool bigMin = false;

      for (int i = unsignedBW; i < bitWidth; i++)
        {
        if  ((*this)[i] == '1' || (*this)[i] == '*')
          bigMax = true;

         if ((*this)[i] == '1')
          bigMin = true;
        }

      for (int i = 0; i < std::min(unsignedBW,bitWidth); i++)
        {
          if ((*this)[i] == '1')
            {
              minShift |= (1 <<i);
              maxShift |= (1 <<i);
            }
          else if ((*this)[i] == '*')
            {
              maxShift |= (1 <<i);
            }
        }

      if (bigMax)
        maxShift = UINT_MAX;

      if (bigMin)
        minShift = UINT_MAX;
    }

    bool
    FixedBits::equals(const FixedBits& a, const FixedBits& b, const int upTo)
    {
      assert (a.getWidth() >= upTo);
      assert (b.getWidth() >= upTo);

      for (int i = 0; i < upTo; i++)
        {
          if (a.isFixed(i) != b.isFixed(i))
            {
              return false;
            }
          if (a.isFixed(i))
            if (a.getValue(i) != b.getValue(i))
              return false;
        }
      return true;
    }

    bool
    FixedBits::equals(const FixedBits& a, const FixedBits& b)
    {
      if (a.getWidth() != b.getWidth())
        return false;

      for (int i = 0; i < a.getWidth(); i++)
        {
          if (a.isFixed(i) != b.isFixed(i))
            {
              return false;
            }
          if (a.isFixed(i))
            if (a.getValue(i) != b.getValue(i))
              return false;
        }
      return true;
    }
  }
}
