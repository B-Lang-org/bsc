#ifndef MULTPLICATIONSTATS_H_
#define MULTPLICATIONSTATS_H_

#include "../../AST/AST.h"
#include <map>
#include "FixedBits.h"

namespace simplifier
{
  namespace constantBitP
  {
    struct MultiplicationStats
    {
    private:

      void
      clear()
      {
        delete[] columnH;
        delete[] columnL;
        delete[] sumL;
        delete[] sumH;

        columnH = NULL;
        columnL = NULL;
        sumL = NULL;
        sumH = NULL;
      }

      void
      copyIn(const MultiplicationStats& f)
      {
        bitWidth = f.bitWidth;
        columnL = new signed[bitWidth];
        columnH = new signed[bitWidth];
        sumL = new signed[bitWidth];
        sumH = new signed[bitWidth];

        for (unsigned i = 0; i < bitWidth; i++)
          {
            columnL[i] = f.columnL[i];
            columnH[i] = f.columnH[i];
            sumL[i] = f.sumL[i];
            sumH[i] = f.sumH[i];
          }
        x = f.x;
        y = f.y;
        r = f.r;
      }

    public:

      signed *columnH; // maximum number of true partial products.
      signed *columnL; // minimum  ""            ""
      signed *sumH;
      signed *sumL;
      unsigned int bitWidth;

      FixedBits x, y, r;

      MultiplicationStats() :
        x(1, false), y(1, false), r(1, false)
      {
        columnH = NULL;
        columnL = NULL;
        sumH = NULL;
        sumL = NULL;
        bitWidth = 0;
      }

      ~MultiplicationStats()
      {
        clear();
      }

      MultiplicationStats(const MultiplicationStats& f) :
        x(f.x), y(f.y), r(f.r)
      {
        copyIn(f);
      }

      MultiplicationStats&
      operator=(const MultiplicationStats& f)
      {
        if (&f == this)
          return *this;

        clear();
        copyIn(f);

        return *this;
      }

      MultiplicationStats(int bitWidth_, signed * columnL_, signed * columnH_, signed * sumL_, signed * sumH_) :
        x(1, false), y(1, false), r(1, false)
      {
        bitWidth = bitWidth_;
        columnL = new signed[bitWidth];
        columnH = new signed[bitWidth];
        sumL = new signed[bitWidth];
        sumH = new signed[bitWidth];

        for (unsigned i = 0; i < bitWidth; i++)
          {
            columnL[i] = columnL_[i];
            columnH[i] = columnH_[i];
            sumL[i] = sumL_[i];
            sumH[i] = sumH_[i];
          }
      }

      void
      print()
      {
        ostream& log = std::cerr;

        log << x << " * " << y << "=" << r << endl;

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

    };

    class MultiplicationStatsMap
    {
    public:
      typedef std::map<BEEV::ASTNode, MultiplicationStats> NodeToStats;
      NodeToStats map;

      void
      print()
      {
        cout << "Size:" << map.size() << endl;

        simplifier::constantBitP::MultiplicationStatsMap::NodeToStats::iterator it;

        for (it = map.begin(); it != map.end(); it++)
          {
            cout << it->first;
            it->second.print();
          }
      }
    };

  };

};

#endif
