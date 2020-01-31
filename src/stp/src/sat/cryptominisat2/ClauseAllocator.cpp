/***********************************************************************
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
************************************************************************/

#include "ClauseAllocator.h"

#include <string.h>
#include <limits>
#include "assert.h"
#include "SolverTypes.h"
#include "Clause.h"
#include "Solver.h"
#include "time_mem.h"
#include "Subsumer.h"
#include "XorSubsumer.h"
//#include "VarReplacer.h"
#include "PartHandler.h"

namespace MINISAT
{
using namespace MINISAT;

//#define DEBUG_CLAUSEALLOCATOR

ClauseAllocator::ClauseAllocator() :
    clausePoolBin(sizeof(Clause) + 2*sizeof(Lit))
{}

ClauseAllocator::~ClauseAllocator()
{
    for (uint32_t i = 0; i < dataStarts.size(); i++) {
        free(dataStarts[i]);
    }
}

template<class T>
Clause* ClauseAllocator::Clause_new(const T& ps, const unsigned int group, const bool learnt)
{
    void* mem = allocEnough(ps.size());
    Clause* real= new (mem) Clause(ps, group, learnt);
    //assert(!(ps.size() == 2 && !real->wasBin()));

    return real;
}
template Clause* ClauseAllocator::Clause_new(const vec<Lit>& ps, const unsigned int group, const bool learnt);
template Clause* ClauseAllocator::Clause_new(const Clause& ps, const unsigned int group, const bool learnt);
template Clause* ClauseAllocator::Clause_new(const XorClause& ps, const unsigned int group, const bool learnt);

template<class T>
XorClause* ClauseAllocator::XorClause_new(const T& ps, const bool inverted, const unsigned int group)
{
    void* mem = allocEnough(ps.size());
    XorClause* real= new (mem) XorClause(ps, inverted, group);
    //assert(!(ps.size() == 2 && !real->wasBin()));

    return real;
}
template XorClause* ClauseAllocator::XorClause_new(const vec<Lit>& ps, const bool inverted, const unsigned int group);
template XorClause* ClauseAllocator::XorClause_new(const XorClause& ps, const bool inverted, const unsigned int group);

Clause* ClauseAllocator::Clause_new(Clause& c)
{
    void* mem = allocEnough(c.size());
    memcpy(mem, &c, sizeof(Clause)+sizeof(Lit)*c.size());
    Clause& c2 = *(Clause*)mem;
    c2.setWasBin(c.size() == 2);
    //assert(!(c.size() == 2 && !c2.wasBin()));
    
    return &c2;
}

#define MIN_LIST_SIZE (300000 * (sizeof(Clause) + 4*sizeof(Lit)))

void* ClauseAllocator::allocEnough(const uint32_t size)
{
    assert(sizes.size() == dataStarts.size());
    assert(maxSizes.size() == dataStarts.size());
    assert(origClauseSizes.size() == dataStarts.size());

    assert(sizeof(Clause)%sizeof(uint32_t) == 0);
    assert(sizeof(Lit)%sizeof(uint32_t) == 0);

    if (size == 2) {
        return clausePoolBin.malloc();
    }
    
    uint32_t needed = sizeof(Clause)+sizeof(Lit)*size;
    bool found = false;
    uint32_t which = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < sizes.size(); i++) {
        if (sizes[i] + needed < maxSizes[i]) {
            found = true;
            which = i;
            break;
        }
    }

    if (!found) {
        #ifdef DEBUG_CLAUSEALLOCATOR
        std::cout << "c New list in ClauseAllocator" << std::endl;
        #endif //DEBUG_CLAUSEALLOCATOR
        
        uint32_t nextSize; //number of BYTES to allocate
        if (maxSizes.size() != 0)
            nextSize = maxSizes[maxSizes.size()-1]*3*sizeof(uint32_t);
        else
            nextSize = MIN_LIST_SIZE;
        assert(needed <  nextSize);
        
        uint32_t *dataStart = (uint32_t*)malloc(nextSize);
        assert(dataStart != NULL);
        dataStarts.push(dataStart);
        sizes.push(0);
        maxSizes.push(nextSize/sizeof(uint32_t));
        origClauseSizes.push();
        currentlyUsedSize.push(0);
        which = dataStarts.size()-1;
    }
    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout
    << "selected list = " << which
    << " size = " << sizes[which]
    << " maxsize = " << maxSizes[which]
    << " diff = " << maxSizes[which] - sizes[which] << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR

    assert(which != std::numeric_limits<uint32_t>::max());
    Clause* pointer = (Clause*)(dataStarts[which] + sizes[which]);
    sizes[which] += needed/sizeof(uint32_t);
    currentlyUsedSize[which] += needed/sizeof(uint32_t);
    origClauseSizes[which].push(needed/sizeof(uint32_t));

    return pointer;
}

const ClauseOffset ClauseAllocator::getOffset(const Clause* ptr) const
{
    uint32_t outerOffset = getOuterOffset(ptr);
    uint32_t interOffset = getInterOffset(ptr, outerOffset);
    return combineOuterInterOffsets(outerOffset, interOffset);
}

inline const ClauseOffset ClauseAllocator::combineOuterInterOffsets(const uint32_t outerOffset, const uint32_t interOffset) const
{
    return (outerOffset | (interOffset<<4));
}

inline uint32_t ClauseAllocator::getOuterOffset(const Clause* ptr) const
{
    uint32_t which = std::numeric_limits<uint32_t>::max();
    for (uint32_t i = 0; i < sizes.size(); i++) {
        if ((uint32_t*)ptr >= dataStarts[i] && (uint32_t*)ptr < dataStarts[i] + maxSizes[i])
            which = i;
    }
    assert(which != std::numeric_limits<uint32_t>::max());

    return which;
}

inline uint32_t ClauseAllocator::getInterOffset(const Clause* ptr, uint32_t outerOffset) const
{
    return ((uint32_t*)ptr - dataStarts[outerOffset]);
}

void ClauseAllocator::clauseFree(Clause* c)
{
    if (c->wasBin()) {
        clausePoolBin.free(c);
    } else {
        c->setFreed();
        uint32_t outerOffset = getOuterOffset(c);
        //uint32_t interOffset = getInterOffset(c, outerOffset);
        currentlyUsedSize[outerOffset] -= (sizeof(Clause) + c->size()*sizeof(Lit))/sizeof(uint32_t);
        //above should be
        //origClauseSizes[outerOffset][interOffset]
        //but it cannot be :(
    }
}

struct NewPointerAndOffset {
    Clause* newPointer;
    uint32_t newOffset;
};

void ClauseAllocator::consolidate(Solver* solver)
{
    double myTime = cpuTime();
    
    //if (dataStarts.size() > 2) {
    uint32_t sum = 0;
    for (uint32_t i = 0; i < sizes.size(); i++) {
        sum += currentlyUsedSize[i];
    }
    uint32_t sumAlloc = 0;
    for (uint32_t i = 0; i < sizes.size(); i++) {
        sumAlloc += sizes[i];
    }

    #ifdef DEBUG_CLAUSEALLOCATOR
    std::cout << "c ratio:" << (double)sum/(double)sumAlloc << std::endl;
    #endif //DEBUG_CLAUSEALLOCATOR
    
    if ((double)sum/(double)sumAlloc > 0.7 /*&& sum > 10000000*/) {
        if (solver->verbosity >= 2) {
            std::cout << "c Not consolidating memory." << std::endl;
        }
        return;
    }

    
    uint32_t newMaxSize = std::max(sum*2*sizeof(uint32_t), MIN_LIST_SIZE);
    uint32_t* newDataStarts = (uint32_t*)malloc(newMaxSize);
    newMaxSize /= sizeof(uint32_t);
    uint32_t newSize = 0;
    vec<uint32_t> newOrigClauseSizes;
    //}

    map<Clause*, Clause*> oldToNewPointer;
    map<uint32_t, uint32_t> oldToNewOffset;
    
    uint32_t* newDataStartsPointer = newDataStarts;
    for (uint32_t i = 0; i < dataStarts.size(); i++) {
        uint32_t currentLoc = 0;
        for (uint32_t i2 = 0; i2 < origClauseSizes[i].size(); i2++) {
            Clause* oldPointer = (Clause*)(dataStarts[i] + currentLoc);
            if (!oldPointer->freed()) {
                uint32_t sizeNeeded = sizeof(Clause) + oldPointer->size()*sizeof(Lit);
                memcpy(newDataStartsPointer, dataStarts[i] + currentLoc, sizeNeeded);
                
                oldToNewPointer[oldPointer] = (Clause*)newDataStartsPointer;
                oldToNewOffset[combineOuterInterOffsets(i, currentLoc)] = combineOuterInterOffsets(0, newSize);

                newSize += sizeNeeded/sizeof(uint32_t);
                newOrigClauseSizes.push(sizeNeeded/sizeof(uint32_t));
                newDataStartsPointer += sizeNeeded/sizeof(uint32_t);
            }
            
            currentLoc += origClauseSizes[i][i2];
        }
    }
    assert(newSize < newMaxSize);
    assert(newSize <= newMaxSize/2);

    updateOffsets(solver->watches, oldToNewOffset);
    updateOffsetsXor(solver->xorwatches, oldToNewOffset);

    updatePointers(solver->clauses, oldToNewPointer);
    updatePointers(solver->learnts, oldToNewPointer);
    updatePointers(solver->binaryClauses, oldToNewPointer);
    updatePointers(solver->xorclauses, oldToNewPointer);

    //No need to update varreplacer, since it only stores binary clauses that
    //must have been allocated such as to use the pool
    //updatePointers(solver->varReplacer->clauses, oldToNewPointer);
    updatePointers(solver->partHandler->clausesRemoved, oldToNewPointer);
    updatePointers(solver->partHandler->xorClausesRemoved, oldToNewPointer);
    for(map<Var, vector<Clause*> >::iterator it = solver->subsumer->elimedOutVar.begin(); it != solver->subsumer->elimedOutVar.end(); it++) {
        updatePointers(it->second, oldToNewPointer);
    }
    for(map<Var, vector<XorClause*> >::iterator it = solver->xorSubsumer->elimedOutVar.begin(); it != solver->xorSubsumer->elimedOutVar.end(); it++) {
        updatePointers(it->second, oldToNewPointer);
    }
    

    vec<PropagatedFrom>& reason = solver->reason;
    for (PropagatedFrom *it = reason.getData(), *end = reason.getDataEnd(); it != end; it++) {
        if (!it->isBinary() && !it->isNULL()) {
            /*if ((it == reason.getData() + (*it->getClause())[0].var())
                && (solver->value((*it->getClause())[0]) == l_True)) {
                assert(oldToNewPointer.find(it->getClause()) != oldToNewPointer.end());
                *it = PropagatedFrom(oldToNewPointer[it->getClause()]);
            } else {
                *it = PropagatedFrom();
            }*/
            if (oldToNewPointer.find(it->getClause()) != oldToNewPointer.end()) {
                *it = PropagatedFrom(oldToNewPointer[it->getClause()]);
            }
        }
    }

    for (uint32_t i = 0; i < dataStarts.size(); i++)
        free(dataStarts[i]);

    dataStarts.clear();
    maxSizes.clear();
    sizes.clear();
    origClauseSizes.clear();

    dataStarts.push(newDataStarts);
    maxSizes.push(newMaxSize);
    sizes.push(newSize);
    currentlyUsedSize.clear();
    currentlyUsedSize.push(newSize);
    origClauseSizes.clear();
    origClauseSizes.push();
    newOrigClauseSizes.moveTo(origClauseSizes[0]);

    if (solver->verbosity >= 1) {
        std::cout << "c Consolidated memory. Time: "
        << cpuTime() - myTime << std::endl;
    }
}

template<class T>
void ClauseAllocator::updateOffsets(vec<vec<T> >& watches, const map<ClauseOffset, ClauseOffset>& oldToNewOffset)
{
    for (uint32_t i = 0;  i < watches.size(); i++) {
        vec<T>& list = watches[i];
        for (T *it = list.getData(), *end = list.getDataEnd(); it != end; it++) {
            map<ClauseOffset, ClauseOffset>::const_iterator it2 = oldToNewOffset.find(it->clause);
            assert(it2 != oldToNewOffset.end());
            it->clause = it2->second;
        }
    }
}

template<class T>
void ClauseAllocator::updateOffsetsXor(vec<vec<T> >& watches, const map<ClauseOffset, ClauseOffset>& oldToNewOffset)
{
    for (uint32_t i = 0;  i < watches.size(); i++) {
        vec<T>& list = watches[i];
        for (T *it = list.getData(), *end = list.getDataEnd(); it != end; it++) {
            map<ClauseOffset, ClauseOffset>::const_iterator it2 = oldToNewOffset.find(*it);
            assert(it2 != oldToNewOffset.end());
            *it = it2->second;
        }
    }
}

template<class T>
void ClauseAllocator::updatePointers(vec<T*>& toUpdate, const map<Clause*, Clause*>& oldToNewPointer)
{
    for (T **it = toUpdate.getData(), **end = toUpdate.getDataEnd(); it != end; it++) {
        if (!(*it)->wasBin()) {
            //assert(oldToNewPointer.find((TT*)*it) != oldToNewPointer.end());
            map<Clause*, Clause*>::const_iterator it2 = oldToNewPointer.find((Clause*)*it);
            *it = (T*)it2->second;
        }
    }
}

void ClauseAllocator::updatePointers(vector<Clause*>& toUpdate, const map<Clause*, Clause*>& oldToNewPointer)
{
    for (vector<Clause*>::iterator it = toUpdate.begin(), end = toUpdate.end(); it != end; it++) {
        if (!(*it)->wasBin()) {
            //assert(oldToNewPointer.find((TT*)*it) != oldToNewPointer.end());
            map<Clause*, Clause*>::const_iterator it2 = oldToNewPointer.find((Clause*)*it);
            *it = it2->second;
        }
    }
}

void ClauseAllocator::updatePointers(vector<XorClause*>& toUpdate, const map<Clause*, Clause*>& oldToNewPointer)
{
    for (vector<XorClause*>::iterator it = toUpdate.begin(), end = toUpdate.end(); it != end; it++) {
        if (!(*it)->wasBin()) {
            //assert(oldToNewPointer.find((TT*)*it) != oldToNewPointer.end());
            map<Clause*, Clause*>::const_iterator it2 = oldToNewPointer.find((Clause*)*it);
            *it = (XorClause*)it2->second;
        }
    }
}

}; //NAMESPACE MINISAT
