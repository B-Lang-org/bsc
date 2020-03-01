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

#include "FindUndef.h"

#include "Solver.h"
#include "VarReplacer.h"
#include <algorithm>

namespace MINISAT
{
using namespace MINISAT;

FindUndef::FindUndef(Solver& _solver) :
    solver(_solver)
    , isPotentialSum(0)
{
}

void FindUndef::fillPotential()
{
    int trail = solver.decisionLevel()-1;
    
    while(trail > 0) {
        assert(trail < (int)solver.trail_lim.size());
        uint at = solver.trail_lim[trail];
        
        assert(at > 0);
        Var v = solver.trail[at].var();
        if (solver.assigns[v] != l_Undef) {
            isPotential[v] = true;
            isPotentialSum++;
        }
        
        trail--;
    }
    
    for (XorClause** it = solver.xorclauses.getData(), **end = it + solver.xorclauses.size(); it != end; it++) {
        XorClause& c = **it;
        for (Lit *l = c.getData(), *end = l + c.size(); l != end; l++) {
            if (isPotential[l->var()]) {
                isPotential[l->var()] = false;
                isPotentialSum--;
            }
            assert(!solver.value(*l).isUndef());
        }
    }
    
    vector<Var> replacingVars = solver.varReplacer->getReplacingVars();
    for (Var *it = &replacingVars[0], *end = it + replacingVars.size(); it != end; it++) {
        if (isPotential[*it]) {
            isPotential[*it] = false;
            isPotentialSum--;
        }
    }
}

void FindUndef::unboundIsPotentials()
{
    for (uint i = 0; i < isPotential.size(); i++)
        if (isPotential[i])
            solver.assigns[i] = l_Undef;
}

void FindUndef::moveBinToNormal()
{
    binPosition = solver.clauses.size();
    for (uint i = 0; i != solver.binaryClauses.size(); i++)
        solver.clauses.push(solver.binaryClauses[i]);
    solver.binaryClauses.clear();
}

void FindUndef::moveBinFromNormal()
{
    for (uint i = binPosition; i != solver.clauses.size(); i++)
        solver.binaryClauses.push(solver.clauses[i]);
    solver.clauses.shrink(solver.clauses.size() - binPosition);
}

const uint FindUndef::unRoll()
{
    if (solver.decisionLevel() == 0) return 0;
    
    moveBinToNormal();
    
    dontLookAtClause.resize(solver.clauses.size(), false);
    isPotential.resize(solver.nVars(), false);
    fillPotential();
    satisfies.resize(solver.nVars(), 0);
    
    while(!updateTables()) {
        assert(isPotentialSum > 0);
        
        uint32_t maximum = 0;
        Var v = var_Undef;
        for (uint i = 0; i < isPotential.size(); i++) {
            if (isPotential[i] && satisfies[i] >= maximum) {
                maximum = satisfies[i];
                v = i;
            }
        }
        assert(v != var_Undef);
        
        isPotential[v] = false;
        isPotentialSum--;
        
        std::fill(satisfies.begin(), satisfies.end(), 0);
    }
    
    unboundIsPotentials();
    moveBinFromNormal();
    
    return isPotentialSum;
}

bool FindUndef::updateTables()
{
    bool allSat = true;
    
    uint i = 0;
    for (Clause** it = solver.clauses.getData(), **end = it + solver.clauses.size(); it != end; it++, i++) {
        if (dontLookAtClause[i])
            continue;
        
        Clause& c = **it;
        bool definitelyOK = false;
        Var v = var_Undef;
        uint numTrue = 0;
        for (Lit *l = c.getData(), *end = l + c.size(); l != end; l++) {
            if (solver.value(*l) == l_True) {
                if (!isPotential[l->var()]) {
                    dontLookAtClause[i] = true;
                    definitelyOK = true;
                    break;
                } else {
                    numTrue ++;
                    v = l->var();
                }
            }
        }
        if (definitelyOK)
            continue;
        
        if (numTrue == 1) {
            assert(v != var_Undef);
            isPotential[v] = false;
            isPotentialSum--;
            dontLookAtClause[i] = true;
            continue;
        }
        
        //numTrue > 1
        allSat = false;
        for (Lit *l = c.getData(), *end = l + c.size(); l != end; l++) {
            if (solver.value(*l) == l_True)
                satisfies[l->var()]++;
        }
    }
    
    return allSat;
}

}; //NAMESPACE MINISAT
