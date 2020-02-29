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

#ifndef PARTHANDLER_H
#define PARTHANDLER_H

#include "Solver.h"
#include "PartFinder.h"
#include "Vec.h"
#include "SolverTypes.h"

#include <map>
#include <vector>
using std::map;
using std::vector;
using std::pair;

namespace MINISAT
{
using namespace MINISAT;

class PartHandler
{
    public:
        PartHandler(Solver& solver);
        const bool handle();
        const vec<lbool>& getSavedState();
        void newVar();
        void addSavedState();
        void readdRemovedClauses();

        friend class ClauseAllocator;
        
    private:
        struct sort_pred {
            bool operator()(const std::pair<int,int> &left, const std::pair<int,int> &right) {
                return left.second < right.second;
            }
        };
        
        //For moving clauses
        void moveClauses(vec<XorClause*>& cs, Solver& newSolver, const uint32_t part, PartFinder& partFinder);
        void moveClauses(vec<Clause*>& cs, Solver& newSolver, const uint32_t part, PartFinder& partFinder);
        void moveLearntClauses(vec<Clause*>& cs, Solver& newSolver, const uint32_t part, PartFinder& partFinder);
        
        //Checking moved clauses
        const bool checkClauseMovement(const Solver& thisSolver, const uint32_t part, const PartFinder& partFinder) const;
        template<class T>
        const bool checkOnlyThisPart(const vec<T*>& cs, const uint32_t part, const PartFinder& partFinder) const;
        
        Solver& solver;
        vec<lbool> savedState;
        vec<Var> decisionVarRemoved; //variables whose decision-ness has been removed
        vec<Clause*> clausesRemoved;
        vec<XorClause*> xorClausesRemoved;
};

inline const vec<lbool>& PartHandler::getSavedState()
{
    return savedState;
}

inline void PartHandler::newVar()
{
    savedState.push(l_Undef);
}

}; //NAMESPACE MINISAT

#endif //PARTHANDLER_H
