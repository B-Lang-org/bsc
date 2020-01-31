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

#ifndef RESTARTTYPECHOOSER_H
#define RESTARTTYPECHOOSER_H

#include "Solver.h"
#include <vector>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "SolverTypes.h"

using std::vector;

namespace MINISAT
{
using namespace MINISAT;

class Solver;

class RestartTypeChooser
{
    public:
        RestartTypeChooser(const Solver& s);
        void addInfo();
        const RestartType choose();
        void reset();
        
    private:
        void calcHeap();
        const double avg() const;
        const std::pair<double, double> countVarsDegreeStDev() const;
        const double stdDeviation(vector<uint32_t>& measure) const;
        
        template<class T>
        void addDegrees(const vec<T*>& cs, vector<uint32_t>& degrees) const;
        
        const Solver& solver;
        const uint32_t topX;
        const uint32_t limit;
        vector<Var> sameIns;
        
        vector<Var> firstVars, firstVarsOld;
};

inline void RestartTypeChooser::reset()
{
    sameIns.clear();
}

}; //NAMESPACE MINISAT

#endif //RESTARTTYPECHOOSER_H
