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

#ifndef CLAUSECLEANER_H
#define CLAUSECLEANER_H

#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Solver.h"
#include "Subsumer.h"
#include "XorSubsumer.h"

namespace MINISAT
{
using namespace MINISAT;

class ClauseCleaner
{
    public:
        ClauseCleaner(Solver& solver);
        
        enum ClauseSetType {clauses, xorclauses, learnts, binaryClauses, simpClauses, xorSimpClauses};
        
        void cleanClauses(vec<Clause*>& cs, ClauseSetType type, const uint limit = 0);
        void cleanClausesBewareNULL(vec<ClauseSimp>& cs, ClauseSetType type, Subsumer& subs, const uint limit = 0);
        void cleanXorClausesBewareNULL(vec<XorClauseSimp>& cs, ClauseSetType type, XorSubsumer& subs, const uint limit = 0);
        const bool cleanClauseBewareNULL(ClauseSimp c, Subsumer& subs);
        const bool cleanXorClauseBewareNULL(XorClauseSimp c, XorSubsumer& subs);
        
        void cleanClauses(vec<XorClause*>& cs, ClauseSetType type, const uint limit = 0);
        void removeSatisfied(vec<Clause*>& cs, ClauseSetType type, const uint limit = 0);
        void removeSatisfied(vec<XorClause*>& cs, ClauseSetType type, const uint limit = 0);
        void removeAndCleanAll(const bool nolimit = false);
        bool satisfied(const Clause& c) const;
        bool satisfied(const XorClause& c) const;

        void moveBinClausesToBinClauses();
        
    private:
        const bool cleanClause(XorClause& c);
        const bool cleanClause(Clause*& c);
        
        uint lastNumUnitarySat[6];
        uint lastNumUnitaryClean[6];
        
        Solver& solver;
};

inline void ClauseCleaner::removeAndCleanAll(const bool nolimit)
{
    //uint limit = std::min((uint)((double)solver.order_heap.size() * PERCENTAGECLEANCLAUSES), FIXCLEANREPLACE);
    uint limit = (double)solver.order_heap.size() * PERCENTAGECLEANCLAUSES;
    if (nolimit) limit = 0;
    
    removeSatisfied(solver.binaryClauses, ClauseCleaner::binaryClauses, limit);
    cleanClauses(solver.clauses, ClauseCleaner::clauses, limit);
    cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses, limit);
    cleanClauses(solver.learnts, ClauseCleaner::learnts, limit);
}

}; //NAMESPACE MINISAT

#endif //CLAUSECLEANER_H
