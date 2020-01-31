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

#ifndef PARTFINDER_H
#define PARTFINDER_H

#include <vector>
#include <map>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Clause.h"

namespace MINISAT
{
using namespace MINISAT;

class Solver;

using std::map;
using std::vector;
using std::pair;

class PartFinder {
    
    public:
        PartFinder(Solver& solver);
        const bool findParts();
        
        const map<uint32_t, vector<Var> >& getReverseTable() const; // part->var
        const uint32_t getVarPart(const Var var) const;
        const vector<uint32_t>& getTable() const; //var -> part
        const vector<Var>& getPartVars(const uint32_t part);
    
    private:
        const uint setParts();
        template<class T>
        void addToPart(const vec<T*>& cs);
        
        struct mysorter
        {
            bool operator () (const pair<uint, uint>& left, const pair<uint, uint>& right)
            {
                return left.second < right.second;
            }
        };
        
        //const bool findParts(vector<Var>& xorFingerprintInMatrix, vector<XorClause*>& xorsInMatrix);
        template<class T>
        void calcIn(const vec<T*>& cs, vector<uint>& numClauseInPart, vector<uint>& sumLitsInPart);
        
        map<uint32_t, vector<Var> > reverseTable; //part -> vars
        vector<uint32_t> table; //var -> part
        uint32_t part_no;
        
        Solver& solver;
};

inline const map<uint32_t, vector<Var> >& PartFinder::getReverseTable() const
{
    return reverseTable;
}

inline const vector<Var>& PartFinder::getTable() const
{
    return table;
}

inline const uint32_t PartFinder::getVarPart(const Var var) const
{
    return table[var];
}

inline const vector<Var>& PartFinder::getPartVars(const uint32_t part)
{
    return reverseTable[part];
}

}; //NAMESPACE MINISAT

#endif //PARTFINDER_H
