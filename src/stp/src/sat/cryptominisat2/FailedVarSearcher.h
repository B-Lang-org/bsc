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

#ifndef FAILEDVARSEARCHER_H
#define FAILEDVARSEARCHER_H

#include <set>
#include <map>
using std::map;

#include "SolverTypes.h"
#include "Clause.h"
#include "BitArray.h"

namespace MINISAT
{
using namespace MINISAT;

class Solver;

class TwoLongXor
{
    public:
        const bool operator==(const TwoLongXor& other) const
        {
            if (var[0] == other.var[0] && var[1] == other.var[1] && inverted == other.inverted)
                return true;
            return false;
        }
        const bool operator<(const TwoLongXor& other) const
        {
            if (var[0] < other.var[0]) return true;
            if (var[0] > other.var[0]) return false;
            
            if (var[1] < other.var[1]) return true;
            if (var[1] > other.var[1]) return false;
            
            if (inverted < other.inverted) return true;
            if (inverted > other.inverted) return false;
            
            return false;
        }
        
        Var var[2];
        bool inverted;
};

class FailedVarSearcher {
    public:
        FailedVarSearcher(Solver& _solver);
    
        const bool search(uint64_t numProps);
        
    private:
        //For 2-long xor
        const TwoLongXor getTwoLongXor(const XorClause& c);
        void addFromSolver(const vec<XorClause*>& cs);
        uint32_t newBinXor;
        
        //For detach&re-attach (when lots of vars found)
        template<class T>
        void cleanAndAttachClauses(vec<T*>& cs);
        const bool cleanClause(Clause& ps);
        const bool cleanClause(XorClause& ps);
        void completelyDetachAndReattach();

        //For re-adding old removed learnt clauses
        const bool readdRemovedLearnts();
        void removeOldLearnts();
        
        //Main
        const bool tryBoth(const Lit lit1, const Lit lit2);
        const bool tryAll(const Lit* begin, const Lit* end);
        void printResults(const double myTime) const;
        
        Solver& solver;
        
        //For failure
        bool failed;
        
        //bothprop finding
        BitArray propagated;
        BitArray propValue;
        vec<Lit> bothSame;
        
        //2-long xor-finding
        vec<uint32_t> xorClauseSizes;
        vector<vector<uint32_t> > occur;
        void removeVarFromXors(const Var var);
        void addVarFromXors(const Var var);
        BitArray xorClauseTouched;
        vec<uint32_t> investigateXor;
        std::set<TwoLongXor> twoLongXors;
        bool binXorFind;
        uint32_t lastTrailSize;
        
        //2-long xor-finding no.2 through
        // 1) (a->b, ~a->~b) -> a=b
        // 2) binary clause (a,c):  (a->g, c->~g) -> a = ~c
        uint32_t bothInvert;

        //finding HyperBins
        void addBinClauses(const Lit& lit);
        BitArray unPropagatedBin;
        vec<Var> propagatedVars;
        void addBin(const Lit& lit1, const Lit& lit2);
        void fillImplies(const Lit& lit);
        BitArray myimplies;
        vec<Var> myImpliesSet;
        uint64_t hyperbinProps;
        vector<uint32_t> litDegrees;
        const bool orderLits();
        uint64_t maxHyperBinProps;
        uint64_t binClauseAdded;

        //Temporaries
        vec<Lit> tmpPs;
        
        //State for this run
        uint32_t toReplaceBefore;
        uint32_t origTrailSize;
        uint64_t origProps;
        uint32_t numFailed;
        uint32_t goodBothSame;
        
        //State between runs
        bool finishedLastTimeVar;
        uint32_t lastTimeWentUntilVar;
        bool finishedLastTimeBin;
        uint32_t lastTimeWentUntilBin;
        
        double numPropsMultiplier;
        uint32_t lastTimeFoundTruths;

        uint32_t numCalls;
};

}; //NAMESPACE MINISAT

#endif //FAILEDVARSEARCHER_H

