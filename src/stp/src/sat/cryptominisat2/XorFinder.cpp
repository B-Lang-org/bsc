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

#include "XorFinder.h"

#include <algorithm>
#include <utility>
#include <iostream>
#include "Solver.h"
#include "VarReplacer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"

//#define VERBOSE_DEBUG
#ifdef _MSC_VER
#define __builtin_prefetch(a,b)
#endif //_MSC_VER

#ifdef VERBOSE_DEBUG
#include <iostream>
using std::cout;
using std::endl;
#endif

namespace MINISAT
{
using namespace MINISAT;

using std::make_pair;

XorFinder::XorFinder(Solver& _solver, vec<Clause*>& _cls, ClauseCleaner::ClauseSetType _type) :
    cls(_cls)
    , type(_type)
    , solver(_solver)
{
}

const bool XorFinder::doNoPart(const uint minSize, const uint maxSize)
{
    uint sumLengths = 0;
    double time = cpuTime();
    foundXors = 0;
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    if (type == ClauseCleaner::binaryClauses) {
        solver.clauseCleaner->cleanClauses(solver.binaryClauses, ClauseCleaner::binaryClauses);
    }
    if (!solver.ok) return false;
    
    toRemove.clear();
    toRemove.resize(cls.size(), false);
    toLeaveInPlace.clear();
    toLeaveInPlace.resize(cls.size(), false);
    
    table.clear();
    table.reserve(cls.size());
    
    ClauseTable unsortedTable;
    unsortedTable.reserve(cls.size());
    ClauseTable sortedTable;
    sortedTable.reserve(cls.size());
    
    for (Clause **it = cls.getData(), **end = it + cls.size(); it != end; it ++) {
        if (it+1 != end)
            __builtin_prefetch(*(it+1), 0);
        //if ((**it)[0].toInt() < (**it)[1].toInt())
        //    std::swap((**it)[0], (**it)[1]);
        Clause& c = (**it);
        if ((*it)->size() != 2) {
            bool sorted = true;
            for (uint i = 0, size = c.size(); i+1 < size ; i++) {
                sorted = (c[i].var() <= c[i+1].var());
                if (!sorted) break;
            }
            if (!sorted) {
                solver.detachClause(c);
                std::sort(c.getData(), c.getDataEnd());
                solver.attachClause(c);
            }
        } else {
            std::sort(c.getData(), c.getData()+c.size());
        }
    }
    
    uint i = 0;
    for (Clause **it = cls.getData(), **end = it + cls.size(); it != end; it++, i++) {
        const uint size = (*it)->size();
        if ( size > maxSize || size < minSize) {
            toLeaveInPlace[i] = true;
            continue;
        }
        if ((*it)->getSorted()) sortedTable.push_back(make_pair(*it, i));
        else unsortedTable.push_back(make_pair(*it, i));
    }
    
    clause_sorter_primary sorter;
    
    std::sort(unsortedTable.begin(), unsortedTable.end(), clause_sorter_primary());
    //std::sort(sortedTable.begin(), sortedTable.end(), clause_sorter_primary());
    #ifdef DEBUG_XORFIND
    for (uint i = 0; i+1 < unsortedTable.size(); i++) {
        assert(!sorter(unsortedTable[i+1], unsortedTable[i]));
    }
    for (uint i = 0; i+1 < sortedTable.size(); i++) {
        assert(!sorter(sortedTable[i+1], sortedTable[i]));
    }
    #endif //DEBUG_XORFIND
    
    for (uint i = 0, j = 0; i < unsortedTable.size() || j <  sortedTable.size();) {
        if (j == sortedTable.size()) {
            table.push_back(unsortedTable[i++]);
            continue;
        }
        if (i == unsortedTable.size()) {
            table.push_back(sortedTable[j++]);
            continue;
        }
        if (sorter(unsortedTable[i], sortedTable[j])) {
            table.push_back(unsortedTable[i++]);
        } else {
            table.push_back(sortedTable[j++]);
        }
    }
    #ifdef DEBUG_XORFIND
    for (uint i = 0; i+1 < table.size(); i++) {
        assert(!sorter(table[i+1], table[i]));
        //table[i].first->plainPrint();
    }
    #endif //DEBUG_XORFIND
    
    if (findXors(sumLengths) == false) goto end;
    solver.ok = (solver.propagate().isNULL());
    
end:
    if (minSize == maxSize && minSize == 2) {
        if (solver.verbosity >= 2 || (solver.conflicts == 0 && solver.verbosity >= 1)) {
            printf("c |  Finding binary XORs:        %5.2lf s (found: %7d, avg size: %3.1lf)                  |\n", cpuTime()-time, foundXors, (double)sumLengths/(double)foundXors);
        }
    } else {
        if (solver.verbosity >= 2 || (solver.verbosity >= 1 && foundXors > 0)) {
            printf("c |  Finding non-binary XORs:    %5.2lf s (found: %7d, avg size: %3.1lf)                  |\n", cpuTime()-time, foundXors, (double)sumLengths/(double)foundXors);
        }
    }
    
    i = 0;
    uint32_t j = 0;
    uint32_t toSkip = 0;
    for (uint end = cls.size(); i != end; i++) {
        if (toLeaveInPlace[i]) {
            cls[j] = cls[i];
            j++;
            toSkip++;
            continue;
        }
        if (!toRemove[table[i-toSkip].second]) {
            table[i-toSkip].first->setSorted();
            cls[j] = table[i-toSkip].first;
            j++;
        }
    }
    cls.shrink(i-j);
    
    return solver.ok;
}

const bool XorFinder::findXors(uint& sumLengths)
{
    #ifdef VERBOSE_DEBUG
    cout << "Finding Xors started" << endl;
    #endif
    
    sumLengths = 0;
    
    ClauseTable::iterator begin = table.begin();
    ClauseTable::iterator end = table.begin();
    vec<Lit> lits;
    bool impair;
    while (getNextXor(begin,  end, impair)) {
        const Clause& c = *(begin->first);
        lits.clear();
        for (const Lit *it = &c[0], *cend = it+c.size() ; it != cend; it++) {
            lits.push(Lit(it->var(), false));
        }
        uint old_group = c.getGroup();
        
        #ifdef VERBOSE_DEBUG
        cout << "- Found clauses:" << endl;
        #endif
        
        for (ClauseTable::iterator it = begin; it != end; it++)
            if (impairSigns(*it->first) == impair){
            #ifdef VERBOSE_DEBUG
            it->first->plainPrint();
            #endif
            toRemove[it->second] = true;
            solver.removeClause(*it->first);
        }
        
        switch(lits.size()) {
        case 2: {
            solver.varReplacer->replace(lits, impair, old_group);
            
            #ifdef VERBOSE_DEBUG
            XorClause* x = XorClause_new(lits, impair, old_group);
            cout << "- Final 2-long xor-clause: ";
            x->plainPrint();
            clauseFree(x);
            #endif
            break;
        }
        default: {
            XorClause* x = solver.clauseAllocator.XorClause_new(lits, impair, old_group);
            solver.xorclauses.push(x);
            solver.attachClause(*x);
            
            #ifdef VERBOSE_DEBUG
            cout << "- Final xor-clause: ";
            x->plainPrint();
            #endif
        }
        }
        
        foundXors++;
        sumLengths += lits.size();
    }
    
    return solver.ok;
}

void XorFinder::clearToRemove()
{
    assert(toRemove.size() == cls.size());
    
    Clause **a = cls.getData();
    Clause **r = cls.getData();
    Clause **cend = cls.getData() + cls.size();
    for (uint i = 0; r != cend; i++) {
        if (!toRemove[i])
            *a++ = *r++;
        else
            r++;
    }
    cls.shrink(r-a);
}

bool XorFinder::getNextXor(ClauseTable::iterator& begin, ClauseTable::iterator& end, bool& impair)
{
    ClauseTable::iterator tableEnd = table.end();

    while(begin != tableEnd && end != tableEnd) {
        begin = end;
        end++;
        uint32_t size = (end == tableEnd ? 0:1);
        while(end != tableEnd && clause_vareq(begin->first, end->first)) {
            size++;
            end++;
        }
        if (size > 0 && isXor(size, begin, end, impair))
            return true;
    }
    
    return false;
}

bool XorFinder::clauseEqual(const Clause& c1, const Clause& c2) const
{
    assert(c1.size() == c2.size());
    for (uint i = 0, size = c1.size(); i < size; i++)
        if (c1[i].sign() !=  c2[i].sign()) return false;
    
    return true;
}

bool XorFinder::impairSigns(const Clause& c) const
{
    uint num = 0;
    for (const Lit *it = &c[0], *end = it + c.size(); it != end; it++)
        num += it->sign();
        
    return num % 2;
}

bool XorFinder::isXor(const uint32_t size, const ClauseTable::iterator& begin, const ClauseTable::iterator& end, bool& impair)
{
    const uint requiredSize = 1 << (begin->first->size()-1);
    
    if (size < requiredSize)
        return false;
    
    #ifdef DEBUG_XORFIND2
    {
        vec<Var> vars;
        Clause& c = *begin->first;
        for (uint i = 0; i < c.size(); i++)
            vars.push(c[i].var());
        for (ClauseTable::iterator it = begin; it != end; it++) {
            Clause& c = *it->first;
            for (uint i = 0; i < c.size(); i++)
                assert(vars[i] == c[i].var());
        }
        clause_sorter_primary sorter;
        
        for (ClauseTable::iterator it = begin; it != end; it++) {
            ClauseTable::iterator it2 = it;
            it2++;
            if (it2 == end) break;
            assert(!sorter(*it2, *it));
        }
    }
    #endif //DEBUG_XORFIND
    
    std::sort(begin, end, clause_sorter_secondary());
    
    uint numPair = 0;
    uint numImpair = 0;
    countImpairs(begin, end, numImpair, numPair);
    
    if (numImpair == requiredSize) {
        impair = true;
        
        return true;
    }
    
    if (numPair == requiredSize) {
        impair = false;
        
        return true;
    }
    
    return false;
}

void XorFinder::countImpairs(const ClauseTable::iterator& begin, const ClauseTable::iterator& end, uint& numImpair, uint& numPair) const
{
    numImpair = 0;
    numPair = 0;
    
    ClauseTable::const_iterator it = begin;
    ClauseTable::const_iterator it2 = begin;
    it2++;
    
    bool impair = impairSigns(*it->first);
    numImpair += impair;
    numPair += !impair;
    
    for (; it2 != end;) {
        if (!clauseEqual(*it->first, *it2->first)) {
            bool impair = impairSigns(*it2->first);
            numImpair += impair;
            numPair += !impair;
        }
        it++;
        it2++;
    }
}

void XorFinder::addAllXorAsNorm()
{
    uint32_t added = 0;
    XorClause **i = solver.xorclauses.getData(), **j = i;
    for (XorClause **end = solver.xorclauses.getDataEnd(); i != end; i++) {
        if ((*i)->size() > 3) {
            *j++ = *i;
            continue;
        }
        added++;
        if ((*i)->size() == 3) addXorAsNormal3(**i);
        //if ((*i)->size() == 4) addXorAsNormal4(**i);
        solver.removeClause(**i);
    }
    solver.xorclauses.shrink(i-j);
    if (solver.verbosity >= 1) {
        std::cout << "c |  Added XOR as norm:" << added << std::endl;
    }
}

void XorFinder::addXorAsNormal3(XorClause& c)
{
    assert(c.size() == 3);
    Clause *tmp;
    vec<Var> vars;
    vec<Lit> vars2(c.size());
    const bool inverted = c.xor_clause_inverted();
    
    for (uint32_t i = 0; i < c.size(); i++) {
        vars.push(c[i].var());
    }
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
}

void XorFinder::addXorAsNormal4(XorClause& c)
{
    assert(c.size() == 4);
    Clause *tmp;
    vec<Var> vars;
    vec<Lit> vars2(c.size());
    const bool inverted = !c.xor_clause_inverted();
    
    for (uint32_t i = 0; i < c.size(); i++) {
        vars.push(c[i].var());
    }
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], false ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], false ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], false ^ inverted);
    vars2[3] = Lit(vars[3], true ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
    
    vars2[0] = Lit(vars[0], true ^ inverted);
    vars2[1] = Lit(vars[1], true ^ inverted);
    vars2[2] = Lit(vars[2], true ^ inverted);
    vars2[3] = Lit(vars[3], false ^ inverted);
    tmp = solver.addClauseInt(vars2, c.getGroup());
    if (tmp) solver.clauses.push(tmp);
}


}; //NAMESPACE MINISAT
