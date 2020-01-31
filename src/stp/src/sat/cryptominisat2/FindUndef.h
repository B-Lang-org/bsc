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

#ifndef FINDUNDEF_H
#define FINDUNDEF_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER
#include <vector>
using std::vector;

#include "Solver.h"

namespace MINISAT
{
using namespace MINISAT;

class FindUndef {
    public:
        FindUndef(Solver& _solver);
        const uint unRoll();
        
    private:
        Solver& solver;
        
        void moveBinToNormal();
        void moveBinFromNormal();
        bool updateTables();
        void fillPotential();
        void unboundIsPotentials();
        
        vector<bool> dontLookAtClause; //If set to TRUE, then that clause already has only 1 lit that is true, so it can be skipped during updateFixNeed()
        vector<uint32_t> satisfies;
        vector<bool> isPotential;
        uint32_t isPotentialSum;
        uint32_t binPosition;
        
};

}; //NAMESPACE MINISAT

#endif //