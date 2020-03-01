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

#include "PartFinder.h"

#include "Solver.h"
#include "Gaussian.h"
#include "GaussianConfig.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "VarReplacer.h"

#include <set>
#include <map>
#include <iomanip>
#include <math.h>
#include "FailedVarSearcher.h"
using std::set;
using std::map;

//#define VERBOSE_DEBUG

using std::cout;
using std::endl;

//#define PART_FINDING

namespace MINISAT
{
using namespace MINISAT;

PartFinder::PartFinder(Solver& _solver) :
    solver(_solver)
{
}

const bool PartFinder::findParts()
{
    assert(solver.performReplace);
    
    double time = cpuTime();
    
    table.clear();
    table.resize(solver.nVars(), std::numeric_limits<uint32_t>::max());
    reverseTable.clear();
    part_no = 0;
    
    solver.clauseCleaner->removeAndCleanAll(true);
    if (!solver.ok) return false;
    while (solver.varReplacer->getNewToReplaceVars() > 0) {
        if (solver.performReplace && !solver.varReplacer->performReplace(true))
            return false;
        solver.clauseCleaner->removeAndCleanAll(true);
        if (!solver.ok) return false;
    }
    assert(solver.varReplacer->getClauses().size() == 0);
    
    addToPart(solver.clauses);
    addToPart(solver.binaryClauses);
    addToPart(solver.xorclauses);
    
    const uint parts = setParts();
    
    #ifndef NDEBUG
    for (map<uint, vector<Var> >::const_iterator it = reverseTable.begin(); it != reverseTable.end(); it++) {
        for (uint i2 = 0; i2 < it->second.size(); i2++) {
            assert(table[(it->second)[i2]] == it->first);
        }
    }
    #endif
    
    if (solver.verbosity >= 2 || (solver.verbosity >=1 && parts > 1)) {
        std::cout << "c | Found parts: " << std::setw(10) <<  parts
        << " time: " << std::setprecision(2) << std::setw(4) << cpuTime() - time
        << " s" << std::setw(51) << " |" << std::endl;
    }
    
    return true;
}

template<class T>
void PartFinder::addToPart(const vec<T*>& cs)
{
    set<uint> tomerge;
    vector<Var> newSet;
    for (T* const* c = cs.getData(), * const*end = c + cs.size(); c != end; c++) {
        if ((*c)->learnt()) continue;
        tomerge.clear();
        newSet.clear();
        for (const Lit *l = (*c)->getData(), *end2 = l + (*c)->size(); l != end2; l++) {
            if (table[l->var()] != std::numeric_limits<uint32_t>::max())
                tomerge.insert(table[l->var()]);
            else
                newSet.push_back(l->var());
        }
        if (tomerge.size() == 1) {
            //no trees to merge, only merge the clause into one tree
            
            const uint into = *tomerge.begin();
            map<uint, vector<Var> >::iterator intoReverse = reverseTable.find(into);
            for (uint i = 0; i < newSet.size(); i++) {
                intoReverse->second.push_back(newSet[i]);
                table[newSet[i]] = into;
            }
            continue;
        }
        
        for (set<uint>::iterator it = tomerge.begin(); it != tomerge.end(); it++) {
            newSet.insert(newSet.end(), reverseTable[*it].begin(), reverseTable[*it].end());
            reverseTable.erase(*it);
        }
        
        for (uint i = 0; i < newSet.size(); i++)
            table[newSet[i]] = part_no;
        reverseTable[part_no] = newSet;
        part_no++;
    }
}

const uint PartFinder::setParts()
{
    vector<uint> numClauseInPart(part_no, 0);
    vector<uint> sumLitsInPart(part_no, 0);
    
    calcIn(solver.clauses, numClauseInPart, sumLitsInPart);
    calcIn(solver.binaryClauses, numClauseInPart, sumLitsInPart);
    calcIn(solver.xorclauses, numClauseInPart, sumLitsInPart);
 
    uint parts = 0;
    for (uint i = 0; i < numClauseInPart.size(); i++) {
        if (sumLitsInPart[i] == 0) continue;
        if (solver.verbosity >= 2 || ( solver.verbosity >= 1 && reverseTable.size() > 1) ) {
            std::cout << "c | Found part " << std::setw(8) << i
            << " vars: " << std::setw(10) << reverseTable[i].size()
            << " clauses:" << std::setw(10) << numClauseInPart[i]
            << " lits size:" << std::setw(10) << sumLitsInPart[i]
            << std::setw(12) << " | " << std::endl;
        }
        parts++;
    }
    
    if (parts > 1) {
        #ifdef VERBOSE_DEBUG
        for (map<uint, vector<Var> >::iterator it = reverseTable.begin(), end = reverseTable.end(); it != end; it++) {
            cout << "-- set begin --" << endl;
            for (vector<Var>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
                cout << *it2 << ", ";
            }
            cout << "-------" << endl;
        }
        #endif
    }
    
    return parts;
}

template<class T>
void PartFinder::calcIn(const vec<T*>& cs, vector<uint>& numClauseInPart, vector<uint>& sumLitsInPart)
{
    for (T*const* c = cs.getData(), *const*end = c + cs.size(); c != end; c++) {
        if ((*c)->learnt()) continue;
        T& x = **c;
        const uint part = table[x[0].var()];
        assert(part < part_no);
        
        //for stats
        numClauseInPart[part]++;
        sumLitsInPart[part] += x.size();
    }
}

}; //NAMESPACE MINISAT
