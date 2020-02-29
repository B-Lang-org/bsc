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

#ifndef MATRIXFINDER_H
#define MATRIXFINDER_H

#include <vector>
#include <map>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Clause.h"
#include "Solver.h"

namespace MINISAT
{
using namespace MINISAT;

class Solver;

using std::map;
using std::vector;
using std::pair;

class MatrixFinder {
    
    public:
        MatrixFinder(Solver& solver);
        const bool findMatrixes();
    
    private:
        const uint setMatrixes();
        
        struct mysorter
        {
            bool operator () (const pair<uint, uint>& left, const pair<uint, uint>& right)
            {
                return left.second < right.second;
            }
        };
        
        void findParts(vector<Var>& xorFingerprintInMatrix, vector<XorClause*>& xorsInMatrix);
        inline const Var fingerprint(const XorClause& c) const;
        inline const bool firstPartOfSecond(const XorClause& c1, const XorClause& c2) const;
        
        map<uint, vector<Var> > reverseTable; //matrix -> vars
        vector<Var> table; //var -> matrix
        uint matrix_no;
        
        Solver& solver;
};

}; //NAMESPACE MINISAT

#endif //MATRIXFINDER_H
