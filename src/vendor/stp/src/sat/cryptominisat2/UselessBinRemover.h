/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#ifndef USELESSBINREMOVER_H
#define USELESSBINREMOVER_H

#include "Vec.h"
#include "Solver.h"
#include "OnlyNonLearntBins.h"
#include <stdint.h>

namespace MINISAT
{
using namespace MINISAT;

class UselessBinRemover {
    public:
        UselessBinRemover(Solver& solver, OnlyNonLearntBins& onlyNonLearntBins);
        const bool removeUslessBinFull();
        
    private:
        bool failed;
        uint32_t extraTime;
        
        //Remove useless binaries
        const bool fillBinImpliesMinusLast(const Lit& origLit, const Lit& lit, vec<Lit>& wrong);
        const bool removeUselessBinaries(const Lit& lit);
        void removeBin(const Lit& lit1, const Lit& lit2);
        vec<char> toDeleteSet;
        vec<Lit> oneHopAway;
        vec<Lit> wrong;

        Solver& solver;
        OnlyNonLearntBins& onlyNonLearntBins;
};

#endif //USELESSBINREMOVER_H

}; //NAMESPACE MINISAT
