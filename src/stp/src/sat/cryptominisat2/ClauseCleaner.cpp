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

#include "ClauseCleaner.h"
#include "VarReplacer.h"

#ifdef _MSC_VER
#define __builtin_prefetch(a,b,c)
#endif //_MSC_VER

//#define DEBUG_CLEAN
//#define VERBOSE_DEBUG

namespace MINISAT
{
using namespace MINISAT;

ClauseCleaner::ClauseCleaner(Solver& _solver) :
    solver(_solver)
{
    for (uint i = 0; i < 6; i++) {
        lastNumUnitarySat[i] = solver.get_unitary_learnts_num();
        lastNumUnitaryClean[i] = solver.get_unitary_learnts_num();
    }
}

void ClauseCleaner::removeSatisfied(vec<XorClause*>& cs, ClauseSetType type, const uint limit)
{
    #ifdef DEBUG_CLEAN
    assert(solver.decisionLevel() == 0);
    #endif
    
    if (lastNumUnitarySat[type] + limit >= solver.get_unitary_learnts_num())
        return;
    
    uint32_t i,j;
    for (i = j = 0; i < cs.size(); i++) {
        if (satisfied(*cs[i]))
            solver.removeClause(*cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
    
    lastNumUnitarySat[type] = solver.get_unitary_learnts_num();
}

void ClauseCleaner::removeSatisfied(vec<Clause*>& cs, ClauseSetType type, const uint limit)
{
    #ifdef DEBUG_CLEAN
    assert(solver.decisionLevel() == 0);
    #endif
    
    if (lastNumUnitarySat[type] + limit >= solver.get_unitary_learnts_num())
        return;
    
    Clause **i,**j, **end;
    for (i = j = cs.getData(), end = i + cs.size(); i != end; i++) {
        if (i+1 != end)
            __builtin_prefetch(*(i+1), 0, 0);
        if (satisfied(**i))
            solver.removeClause(**i);
        else
            *j++ = *i;
    }
    cs.shrink(i - j);
    
    lastNumUnitarySat[type] = solver.get_unitary_learnts_num();
}

void ClauseCleaner::cleanClauses(vec<Clause*>& cs, ClauseSetType type, const uint limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());
    
    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;

    #ifdef VERBOSE_DEBUG
    std::cout << "Cleaning " << (type==binaryClauses ? "binaryClauses" : "normal clauses" ) << std::endl;
    #endif //VERBOSE_DEBUG
    
    Clause **s, **ss, **end;
    for (s = ss = cs.getData(), end = s + cs.size();  s != end;) {
        if (s+1 != end)
            __builtin_prefetch(*(s+1), 1, 0);
        if (cleanClause(*s)) {
            solver.clauseAllocator.clauseFree(*s);
            s++;
        } else if (type != ClauseCleaner::binaryClauses && (*s)->size() == 2) {
            solver.binaryClauses.push(*s);
            solver.becameBinary++;
            s++;
        } else {
            *ss++ = *s++;
        }
    }
    cs.shrink(s-ss);
    
    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();
    
    #ifdef VERBOSE_DEBUG
    cout << "cleanClauses(Clause) useful ?? Removed: " << s-ss << endl;
    #endif
}

inline const bool ClauseCleaner::cleanClause(Clause*& cc)
{
    Clause& c = *cc;
    
    Lit origLit1 = c[0];
    Lit origLit2 = c[1];
    uint32_t origSize = c.size();
    
    Lit *i, *j, *end;
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }
        
        if (val == l_True) {
            solver.detachModifiedClause(origLit1, origLit2, origSize, &c);
            return true;
        }
    }
    c.shrink(i-j);

    assert(c.size() != 1);
    if (i != j) {
        c.setStrenghtened();
        if (c.size() == 2) {
            solver.detachModifiedClause(origLit1, origLit2, origSize, &c);
            Clause *c2 = solver.clauseAllocator.Clause_new(c);
            solver.clauseAllocator.clauseFree(&c);
            cc = c2;
            solver.attachClause(*c2);
        } else {
            if (c.learnt())
                solver.learnts_literals -= i-j;
            else
                solver.clauses_literals -= i-j;
        }
    }
    
    return false;
}

void ClauseCleaner::cleanClauses(vec<XorClause*>& cs, ClauseSetType type, const uint limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());
    
    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;
    
    XorClause **s, **ss, **end;
    for (s = ss = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end)
            __builtin_prefetch(*(s+1), 1, 0);

        #ifdef DEBUG_ATTACH
        assert(find(solver.xorwatches[(**s)[0].var()], *s));
        assert(find(solver.xorwatches[(**s)[1].var()], *s));
        if (solver.assigns[(**s)[0].var()]!=l_Undef || solver.assigns[(**s)[1].var()]!=l_Undef) {
            satisfied(**s);
        }
        #endif //DEBUG_ATTACH
        
        if (cleanClause(**s)) {
            solver.freeLater.push(*s);
            (*s)->setRemoved();
        } else {
            #ifdef DEBUG_ATTACH
            assert(find(solver.xorwatches[(**s)[0].var()], *s));
            assert(find(solver.xorwatches[(**s)[1].var()], *s));
            #endif //DEBUG_ATTACH
            *ss++ = *s;
        }
    }
    cs.shrink(s-ss);
    
    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();
    
    #ifdef VERBOSE_DEBUG
    cout << "cleanClauses(XorClause) useful: ?? Removed: " << s-ss << endl;
    #endif
}

inline const bool ClauseCleaner::cleanClause(XorClause& c)
{
    Lit *i, *j, *end;
    Var origVar1 = c[0].var();
    Var origVar2 = c[1].var();
    uint32_t origSize = c.size();
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        const lbool& val = solver.assigns[i->var()];
        if (val.isUndef()) {
            *j = *i;
            j++;
        } else c.invert(val.getBool());
    }
    c.shrink(i-j);
    
    assert(c.size() != 1);
    switch (c.size()) {
        case 0: {
            solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
            return true;
        }
        case 2: {
            c[0] = c[0].unsign();
            c[1] = c[1].unsign();
            solver.varReplacer->replace(c, c.xor_clause_inverted(), c.getGroup());
            solver.detachModifiedClause(origVar1, origVar2, origSize, &c);
            return true;
        }
        default: {
            if (i-j > 0) {
                c.setStrenghtened();
                solver.clauses_literals -= i-j;
            }
            return false;
        }
    }

    assert(false);
    return false;
}

void ClauseCleaner::cleanClausesBewareNULL(vec<ClauseSimp>& cs, ClauseCleaner::ClauseSetType type, Subsumer& subs, const uint limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());
    
    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;
    
    ClauseSimp *s, *end;
    for (s = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end)
            __builtin_prefetch((s+1)->clause, 1, 0);
        if (s->clause == NULL)
            continue;
        
        if (cleanClauseBewareNULL(*s, subs)) {
            continue;
        } else if (s->clause->size() == 2)
            solver.becameBinary++;
    }
    
    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();
}

inline const bool ClauseCleaner::cleanClauseBewareNULL(ClauseSimp cc, Subsumer& subs)
{
    Clause& c = *cc.clause;
    vec<Lit> origClause(c.size());
    memcpy(origClause.getData(), c.getData(), sizeof(Lit)*c.size());
    
    Lit *i, *j, *end;
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        lbool val = solver.value(*i);
        if (val == l_Undef) {
            *j++ = *i;
            continue;
        }
        
        if (val == l_True) {
            subs.unlinkModifiedClause(origClause, cc, true);
            solver.clauseAllocator.clauseFree(cc.clause);
            return true;
        }
    }
    
    if (i != j) {
        c.setStrenghtened();
        if (origClause.size() > 2 && origClause.size()-(i-j) == 2) {
            subs.unlinkModifiedClause(origClause, cc, true);
            subs.clauses[cc.index] = cc;
            c.shrink(i-j);
            solver.attachClause(c);
            subs.linkInAlreadyClause(cc);
        } else {
            c.shrink(i-j);
            subs.unlinkModifiedClause(origClause, cc, false);
            subs.linkInAlreadyClause(cc);
            if (c.learnt())
                solver.learnts_literals -= i-j;
            else
                solver.clauses_literals -= i-j;
        }
        if (!c.learnt()) c.calcAbstractionClause();
        subs.updateClause(cc);
    }
    
    return false;
}

void ClauseCleaner::cleanXorClausesBewareNULL(vec<XorClauseSimp>& cs, ClauseCleaner::ClauseSetType type, XorSubsumer& subs, const uint limit)
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());
    
    if (lastNumUnitaryClean[type] + limit >= solver.get_unitary_learnts_num())
        return;
    
    XorClauseSimp *s, *end;
    for (s = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end)
            __builtin_prefetch((s+1)->clause, 1, 0);
        if (s->clause == NULL)
            continue;
        
        cleanXorClauseBewareNULL(*s, subs);
    }
    
    lastNumUnitaryClean[type] = solver.get_unitary_learnts_num();
}

inline const bool ClauseCleaner::cleanXorClauseBewareNULL(XorClauseSimp cc, XorSubsumer& subs)
{
    XorClause& c = *cc.clause;
    vec<Lit> origClause(c.size());
    memcpy(origClause.getData(), c.getData(), sizeof(Lit)*c.size());
    
    Lit *i, *j, *end;
    for (i = j = c.getData(), end = i + c.size();  i != end; i++) {
        const lbool& val = solver.assigns[i->var()];
        if (val.isUndef()) {
            *j = *i;
            j++;
        } else c.invert(val.getBool());
    }
    c.shrink(i-j);
    
    switch(c.size()) {
        case 0: {
            subs.unlinkModifiedClause(origClause, cc);
            solver.clauseAllocator.clauseFree(cc.clause);
            return true;
        }
        case 2: {
            vec<Lit> ps(2);
            ps[0] = c[0].unsign();
            ps[1] = c[1].unsign();
            solver.varReplacer->replace(ps, c.xor_clause_inverted(), c.getGroup());
            subs.unlinkModifiedClause(origClause, cc);
            solver.clauseAllocator.clauseFree(cc.clause);
            return true;
        }
        default:
            if (i-j > 0) {
                subs.unlinkModifiedClauseNoDetachNoNULL(origClause, cc);
                subs.linkInAlreadyClause(cc);
                c.calcXorAbstraction();
            }
    }
    
    return false;
}

bool ClauseCleaner::satisfied(const Clause& c) const
{
    for (uint i = 0; i != c.size(); i++)
        if (solver.value(c[i]) == l_True)
            return true;
        return false;
}

bool ClauseCleaner::satisfied(const XorClause& c) const
{
    bool final = c.xor_clause_inverted();
    for (uint k = 0; k != c.size(); k++ ) {
        const lbool& val = solver.assigns[c[k].var()];
        if (val.isUndef()) return false;
        final ^= val.getBool();
    }
    return final;
}

void ClauseCleaner::moveBinClausesToBinClauses()
{
    assert(solver.decisionLevel() == 0);
    assert(solver.qhead == solver.trail.size());

    vec<Clause*>& cs = solver.clauses;
    Clause **s, **ss, **end;
    for (s = ss = cs.getData(), end = s + cs.size();  s != end; s++) {
        if (s+1 != end)
            __builtin_prefetch(*(s+1), 1, 0);

        if ((**s).size() == 2) {
            solver.detachClause(**s);
            Clause *c2 = solver.clauseAllocator.Clause_new(**s);
            solver.clauseAllocator.clauseFree(*s);
            solver.attachClause(*c2);
            solver.becameBinary++;
            solver.binaryClauses.push(c2);
        } else
            *ss++ = *s;
    }
    cs.shrink(s-ss);
}

}; //NAMESPACE MINISAT
