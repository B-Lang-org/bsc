/**************************************************************************************************
Originally From: Solver.C -- (C) Niklas Een, Niklas Sorensson, 2004
Substantially modified by: Mate Soos (2010)
**************************************************************************************************/

#include "Solver.h"
#include "Subsumer.h"
#include "ClauseCleaner.h"
#include "time_mem.h"
#include "assert.h"
#include <iomanip>
#include <cmath>
#include <algorithm>
#include "VarReplacer.h"
#include "XorFinder.h"
#include "OnlyNonLearntBins.h"

#ifdef _MSC_VER
#define __builtin_prefetch(a,b,c)
#endif //_MSC_VER

//#define VERBOSE_DEBUG
#ifdef VERBOSE_DEBUG
#define BIT_MORE_VERBOSITY
#endif

//#define BIT_MORE_VERBOSITY
//#define TOUCH_LESS

#ifdef VERBOSE_DEBUG
using std::cout;
using std::endl;
#endif //VERBOSE_DEBUG

namespace MINISAT
{
using namespace MINISAT;

Subsumer::Subsumer(Solver& s):
    solver(s)
    , totalTime(0.0)
    , numElimed(0)
    , numCalls(0)
{
};

Subsumer::~Subsumer()
{
}

void Subsumer::extendModel(Solver& solver2)
{
    assert(checkElimedUnassigned());
    vec<Lit> tmp;
    typedef map<Var, vector<Clause*> > elimType;
    for (elimType::iterator it = elimedOutVar.begin(), end = elimedOutVar.end(); it != end; it++) {
        #ifndef NDEBUG
        Var var = it->first;
        #ifdef VERBOSE_DEBUG
        std::cout << "Reinserting elimed var: " << var+1 << std::endl;
        #endif
        assert(!solver.decision_var[var]);
        assert(solver.assigns[var] == l_Undef);
        assert(!solver.order_heap.inHeap(var));
        #endif
        
        for (vector<Clause*>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
            Clause& c = **it2;
            tmp.clear();
            tmp.growTo(c.size());
            std::copy(c.getData(), c.getDataEnd(), tmp.getData());
            
            #ifdef VERBOSE_DEBUG
            std::cout << "Reinserting Clause: ";
            c.plainPrint();
            #endif
            
            solver2.addClause(tmp);
            assert(solver2.ok);
        }
    }
}

const bool Subsumer::unEliminate(const Var var)
{
    assert(var_elimed[var]);
    vec<Lit> tmp;
    typedef map<Var, vector<Clause*> > elimType;
    elimType::iterator it = elimedOutVar.find(var);

    //it MUST have been decision var, otherwise we would
    //never have removed it
    solver.setDecisionVar(var, true);
    var_elimed[var] = false;
    numElimed--;
    
    //If the variable was removed because of
    //pure literal removal (by blocked clause
    //elimination, there are no clauses to re-insert
    if (it == elimedOutVar.end()) return solver.ok;
    
    FILE* backup_libraryCNFfile = solver.libraryCNFFile;
    solver.libraryCNFFile = NULL;
    for (vector<Clause*>::iterator it2 = it->second.begin(), end2 = it->second.end(); it2 != end2; it2++) {
        solver.addClause(**it2);
        solver.clauseAllocator.clauseFree(*it2);
    }
    solver.libraryCNFFile = backup_libraryCNFfile;
    elimedOutVar.erase(it);
    
    return solver.ok;
}

bool selfSubset(uint32_t A, uint32_t B)
{
    uint32_t B_tmp = B | ((B & 0xAAAAAAAALL) >> 1) | ((B & 0x55555555LL) << 1);
    if ((A & ~B_tmp) == 0){
        uint32_t C = A & ~B;
        return (C & (C-1)) == 0;
    }else
        return false;
}

// Assumes 'seen' is cleared (will leave it cleared)
bool selfSubset(Clause& A, Clause& B, vec<char>& seen)
{
    for (uint32_t i = 0; i < B.size(); i++)
        seen[B[i].toInt()] = 1;
    
    bool    flip = false;
    for (uint32_t i = 0; i < A.size(); i++) {
        if (!seen[A[i].toInt()]) {
            if (flip == true || !seen[(~A[i]).toInt()]) {
                for (uint32_t i = 0; i < B.size(); i++) seen[B[i].toInt()] = 0;
                return false;
            }
            flip = true;
        }
    }
    for (uint32_t i = 0; i < B.size(); i++)
        seen[B[i].toInt()] = 0;
    return flip;
}

template <>
inline uint32_t Subsumer::subsume0(Clause& ps, uint32_t abs)
{
    ps.subsume0Finished();
    ps.unsetVarChanged();
    #ifdef VERBOSE_DEBUG
    cout << "subsume0 orig clause: ";
    ps.plainPrint();
    #endif
    return subsume0Orig(ps, abs);
}

template <class T>
inline uint32_t Subsumer::subsume0(T& ps, uint32_t abs)
{
    #ifdef VERBOSE_DEBUG
    cout << "subsume0 orig vec: ";
    ps[0].print(); std::cout << " ";
    ps[1].printFull();
    #endif
    return subsume0Orig(ps, abs);
}

// Will put NULL in 'cs' if clause removed.
template<class T>
uint32_t Subsumer::subsume0Orig(const T& ps, uint32_t abs)
{
    subsumedNonLearnt = false;
    uint32_t retIndex = std::numeric_limits<uint32_t>::max();
    vec<ClauseSimp> subs;
    findSubsumed(ps, abs, subs);
    for (uint32_t i = 0; i < subs.size(); i++){
        clauses_subsumed++;
        #ifdef VERBOSE_DEBUG
        cout << "-> subsume0 removing:";
        subs[i].clause->plainPrint();
        #endif
        
        Clause* tmp = subs[i].clause;
        subsumedNonLearnt |= !tmp->learnt();
        retIndex = subs[i].index;
        unlinkClause(subs[i]);
        solver.clauseAllocator.clauseFree(tmp);
    }
    
    return retIndex;
}

void Subsumer::subsume0BIN(const Lit lit1, const vec<char>& lits)
{
    vec<ClauseSimp> subs;
    vec<ClauseSimp> subs2;
    vec<Lit> subs2Lit;

    vec<ClauseSimp>& cs = occur[lit1.toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 0, 1);
        if (it->clause == NULL) continue;
        Clause& c = *it->clause;
        bool removed = false;
        for (uint32_t i = 0; i < c.size(); i++) {
            if (lits[c[i].toInt()]) {
                subs.push(*it);
                removed = true;
                break;
            }
        }
        if (!removed) {
            for (uint32_t i = 0; i < c.size(); i++) {
                if (lits[(~c[i]).toInt()]) {
                    subs2.push(*it);
                    subs2Lit.push(c[i]);
                    break;
                }
            }
        }
    }
    
    for (uint32_t i = 0; i < subs.size(); i++){
        clauses_subsumed++;
        #ifdef VERBOSE_DEBUG
        cout << "-> subsume0 removing:";
        subs[i].clause->plainPrint();
        #endif
        
        Clause* tmp = subs[i].clause;
        unlinkClause(subs[i]);
        solver.clauseAllocator.clauseFree(tmp);
    }

    if (subs2.size() == 0) return;
    registerIteration(subs2);
    for (uint32_t j = 0; j < subs2.size(); j++){
        if (subs2[j].clause == NULL) continue;
        ClauseSimp c = subs2[j];
        Clause& cl = *c.clause;
        #ifdef VERBOSE_DEBUG
        cout << "-> Strenghtening clause :";
        cl.plainPrint();
        #endif
        unlinkClause(c);

        literals_removed++;
        cl.strengthen(subs2Lit[j]);
        Lit *a, *b, *end;
        for (a = b = cl.getData(), end = a + cl.size();  a != end; a++) {
            lbool val = solver.value(*a);
            if (val == l_Undef)
                *b++ = *a;

            if (val == l_True) {
                #ifdef VERBOSE_DEBUG
                std::cout << "--> Clause was satisfied." << std::endl;
                #endif
                solver.clauseAllocator.clauseFree(&cl);
                goto endS;
            }
        }
        cl.shrink(a-b);
        cl.setStrenghtened();

        #ifdef VERBOSE_DEBUG
        cout << "--> Strenghtened clause:";
        cl.plainPrint();
        #endif

        if (cl.size() == 0) {
            solver.ok = false;
            unregisterIteration(subs2);
            solver.clauseAllocator.clauseFree(&cl);
            return;
        }
        if (cl.size() > 2) {
            cl.calcAbstractionClause();
            linkInAlreadyClause(c);
            clauses[c.index] = c;
            solver.attachClause(cl);
            updateClause(c);
        } else if (cl.size() == 2) {
            cl.calcAbstractionClause();
            solver.attachClause(cl);
            solver.becameBinary++;
            addBinaryClauses.push(&cl);
            //updateClause(c);
        } else {
            assert(cl.size() == 1);
            solver.uncheckedEnqueue(cl[0]);
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) {
                unregisterIteration(subs2);
                return;
            }
            #ifdef VERBOSE_DEBUG
            cout << "--> Found that var " << cl[0].var()+1 << " must be " << std::boolalpha << !cl[0].sign() << endl;
            #endif
            solver.clauseAllocator.clauseFree(&cl);
        }
        endS:;
    }
    unregisterIteration(subs2);
}

void Subsumer::unlinkClause(ClauseSimp c, Var elim)
{
    Clause& cl = *c.clause;
    
    if (elim != var_Undef) {
        assert(!cl.learnt());
        #ifdef VERBOSE_DEBUG
        std::cout << "Eliminating clause: "; c.clause->plainPrint();
        std::cout << "On variable: " << elim+1 << std::endl;
        #endif //VERBOSE_DEBUG
        elimedOutVar[elim].push_back(c.clause);
    }

    for (uint32_t i = 0; i < cl.size(); i++) {
        maybeRemove(occur[cl[i].toInt()], &cl);
        #ifndef TOUCH_LESS
        touch(cl[i]);
        #endif
    }
    
    solver.detachClause(cl);
    
    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_vecs.size(); i++) {
        vec<ClauseSimp>& cs = *iter_vecs[i];
        for (uint32_t j = 0; j < cs.size(); j++)
            if (cs[j].clause == &cl)
                cs[j].clause = NULL;
    }
    for (uint32_t i = 0; i < iter_sets.size(); i++) {
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }
    
    // Remove clause from clause touched set:
    cl_touched.exclude(c);
    cl_added.exclude(c);
    
    clauses[c.index].clause = NULL;
}

void Subsumer::unlinkModifiedClause(vec<Lit>& origClause, ClauseSimp c, bool detachAndNull)
{
    for (uint32_t i = 0; i < origClause.size(); i++) {
        maybeRemove(occur[origClause[i].toInt()], c.clause);
        #ifndef TOUCH_LESS
        touch(origClause[i]);
        #endif
    }
    
    // Remove from iterator vectors/sets:
    for (uint32_t i = 0; i < iter_vecs.size(); i++){
        vec<ClauseSimp>& cs = *iter_vecs[i];
        for (uint32_t j = 0; j < cs.size(); j++)
            if (cs[j].clause == c.clause)
                cs[j].clause = NULL;
    }
    for (uint32_t i = 0; i < iter_sets.size(); i++){
        CSet& cs = *iter_sets[i];
        cs.exclude(c);
    }
    
    // Remove clause from clause touched set:
    cl_touched.exclude(c);
    cl_added.exclude(c);

    if (detachAndNull) {
        solver.detachModifiedClause(origClause[0], origClause[1], origClause.size(), c.clause);
        clauses[c.index].clause = NULL;
    }
}

void Subsumer::subsume1(ClauseSimp& ps)
{
    vec<ClauseSimp>    Q;
    vec<ClauseSimp>    subs;
    vec<Lit>        qs;
    uint32_t        q;
    
    ps.clause->unsetStrenghtened();
    registerIteration(Q);
    registerIteration(subs);
    
    Q.push(ps);
    q = 0;
    while (q < Q.size()){
        if (Q[q].clause == NULL) { q++; continue; }
        #ifdef VERBOSE_DEBUG
        cout << "subsume1 with clause:";
        Q[q].clause->plainPrint();
        #endif
        
        qs.clear();
        for (uint32_t i = 0; i < Q[q].clause->size(); i++)
            qs.push((*Q[q].clause)[i]);
        
        for (uint32_t i = 0; i < qs.size(); i++){
            qs[i] = ~qs[i];
            
            uint32_t abst = calcAbstraction(qs);
            
            findSubsumed(qs, abst, subs);
            for (uint32_t j = 0; j < subs.size(); j++){
                /*#ifndef NDEBUG
                if (&counter != NULL && counter == -1){
                    dump(*subs[j].clause);
                    qs[i] = ~qs[i];
                    dump(qs);
                    printf(L_LIT"\n", L_lit(qs[i]));
                    exit(0);
                }
                #endif*/
                if (subs[j].clause == NULL) continue;
                ClauseSimp c = subs[j];
                Clause& cl = *c.clause;
                #ifdef VERBOSE_DEBUG
                cout << "-> Strenghtening clause :";
                cl.plainPrint();
                #endif
                unlinkClause(c);
                
                literals_removed++;
                cl.strengthen(qs[i]);
                Lit *a, *b, *end;
                for (a = b = cl.getData(), end = a + cl.size();  a != end; a++) {
                    lbool val = solver.value(*a);
                    if (val == l_Undef)
                        *b++ = *a;
                    
                    if (val == l_True) {
                        #ifdef VERBOSE_DEBUG
                        std::cout << "--> Clause was satisfied." << std::endl;
                        #endif
                        solver.clauseAllocator.clauseFree(&cl);
                        goto endS;
                    }
                }
                cl.shrink(a-b);
                cl.setStrenghtened();
                
                #ifdef VERBOSE_DEBUG
                cout << "--> Strenghtened clause:";
                cl.plainPrint();
                #endif
                
                if (cl.size() == 0) {
                    solver.ok = false;
                    unregisterIteration(Q);
                    unregisterIteration(subs);
                    solver.clauseAllocator.clauseFree(&cl);
                    return;
                }
                if (cl.size() > 1) {
                    cl.calcAbstractionClause();
                    linkInAlreadyClause(c);
                    clauses[c.index] = c;
                    solver.attachClause(cl);
                    if (cl.size() == 2) solver.becameBinary++;
                    updateClause(c);
                    Q.push(c);
                } else {
                    assert(cl.size() == 1);
                    solver.uncheckedEnqueue(cl[0]);
                    solver.ok = (solver.propagate().isNULL());
                    if (!solver.ok) {
                        unregisterIteration(Q);
                        unregisterIteration(subs);
                        return;
                    }
                    #ifdef VERBOSE_DEBUG
                    cout << "--> Found that var " << cl[0].var()+1 << " must be " << std::boolalpha << !cl[0].sign() << endl;
                    #endif
                    solver.clauseAllocator.clauseFree(&cl);
                }
                endS:;
            }
            
            qs[i] = ~qs[i];
            subs.clear();
        }
        q++;
    }
    
    unregisterIteration(Q);
    unregisterIteration(subs);
}

template<class T>
void Subsumer::subsume1Partial(const T& ps)
{
    assert(solver.decisionLevel() == 0);
    registerIteration(subsume1PartialSubs);
    
    #ifdef VERBOSE_DEBUG
    cout << "-> Strenghtening using clause :";
    ps[0].print(); std::cout << " ";
    ps[1].printFull();
    #endif

    assert(ps.size() == 2);
    subsume1PartialQs.clear();
    for (uint8_t i = 0; i < 2; i++)
        subsume1PartialQs.push(ps[i]);

    for (uint8_t i = 0; i < 2; i++){
        subsume1PartialQs[i] = ~subsume1PartialQs[i];

        uint32_t abst = calcAbstraction(subsume1PartialQs);

        findSubsumed(subsume1PartialQs, abst, subsume1PartialSubs);
        for (uint32_t j = 0; j < subsume1PartialSubs.size(); j++){
            if (subsume1PartialSubs[j].clause == NULL) continue;
            ClauseSimp c = subsume1PartialSubs[j];
            Clause& cl = *c.clause;
            #ifdef VERBOSE_DEBUG
            cout << "-> Strenghtening clause :";
            cl.plainPrint();
            #endif
            unlinkClause(subsume1PartialSubs[j]);

            literals_removed++;
            cl.strengthen(subsume1PartialQs[i]);
            Lit *a, *b, *end;
            for (a = b = cl.getData(), end = a + cl.size();  a != end; a++) {
                lbool val = solver.value(*a);
                if (val == l_Undef)
                    *b++ = *a;

                if (val == l_True) {
                    #ifdef VERBOSE_DEBUG
                    std::cout << "--> Clause was satisfied." << std::endl;
                    #endif
                    solver.clauseAllocator.clauseFree(&cl);
                    goto endS;
                }
            }
            cl.shrink(a-b);
            cl.setStrenghtened();

            #ifdef VERBOSE_DEBUG
            cout << "--> Strenghtened clause:";
            cl.plainPrint();
            #endif

            if (cl.size() == 0) {
                solver.ok = false;
                unregisterIteration(subsume1PartialSubs);
                solver.clauseAllocator.clauseFree(&cl);
                return;
            }
            if (cl.size() > 2) {
                cl.calcAbstractionClause();
                linkInAlreadyClause(c);
                clauses[c.index] = c;
                solver.attachClause(cl);
                updateClause(c);
            } else if (cl.size() == 2) {
                cl.calcAbstractionClause();
                solver.attachClause(cl);
                solver.becameBinary++;
                addBinaryClauses.push(&cl);
                //updateClause(c);
            } else {
                assert(cl.size() == 1);
                solver.uncheckedEnqueue(cl[0]);
                solver.ok = (solver.propagate().isNULL());
                if (!solver.ok) {
                    unregisterIteration(subsume1PartialSubs);
                    return;
                }
                #ifdef VERBOSE_DEBUG
                cout << "--> Found that var " << cl[0].var()+1 << " must be " << std::boolalpha << !cl[0].sign() << endl;
                #endif
                solver.clauseAllocator.clauseFree(&cl);
            }
            endS:;
        }

        subsume1PartialQs[i] = ~subsume1PartialQs[i];
        subsume1PartialSubs.clear();
    }
    unregisterIteration(subsume1PartialSubs);
}

void Subsumer::updateClause(ClauseSimp c)
{
    subsume0(*c.clause, c.clause->getAbst());
    if (c.clause->learnt() && subsumedNonLearnt)
        c.clause->makeNonLearnt();
    
    cl_touched.add(c);
}

void Subsumer::almost_all_database()
{
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c Larger database" << std::endl;
    #endif
    // Optimized variant when virtually whole database is involved:
    cl_added  .clear();
    cl_touched.clear();
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (numMaxSubsume1 == 0) break;
        if (clauses[i].clause != NULL) {
            subsume1(clauses[i]);
            numMaxSubsume1--;
            if (!solver.ok) return;
        }
    }
    
    assert(solver.ok);
    solver.ok = (solver.propagate().isNULL());
    if (!solver.ok) {
        return;
    }
    solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
    
    #ifdef VERBOSE_DEBUG
    cout << "subsume1 part 1 finished" << endl;
    #endif
    
    CSet s1;
    registerIteration(s1);
    while (cl_touched.size() > 0 && numMaxSubsume1 > 0){
        #ifdef VERBOSE_DEBUG
        std::cout << "c cl_touched was > 0, new iteration" << std::endl;
        #endif
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause != NULL)
                s1.add(*it);
        }
        cl_touched.clear();
        
        for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
            if (numMaxSubsume1 == 0) break;
            if (it->clause != NULL) {
                subsume1(*it);
                numMaxSubsume1--;
                if (!solver.ok) return;
            }
        }
        s1.clear();
        
        if (!solver.ok) return;
        solver.ok = (solver.propagate().isNULL());
        if (!solver.ok) {
            unregisterIteration(s1);
            return;
        }
        solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
    }
    unregisterIteration(s1);
}

void Subsumer::smaller_database()
{
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c Smaller database" << std::endl;
    #endif
    //  Set used in 1-subs:
    //      (1) clauses containing a negated literal of an added clause.
    //      (2) all added or strengthened ("touched") clauses.
    //
    //  Set used in 0-subs:
    //      (1) clauses containing a (non-negated) literal of an added clause, including the added clause itself.
    //      (2) all strenghtened clauses -- REMOVED!! We turned on eager backward subsumption which supersedes this.
    
    #ifdef BIT_MORE_VERBOSITY
    printf("  PREPARING\n");
    #endif
    
    CSet s0, s1;     // 's0' is used for 0-subsumption, 's1' for 1-subsumption
    vec<char>   ol_seen(solver.nVars()*2, 0);
    for (CSet::iterator it = cl_added.begin(), end = cl_added.end(); it != end; ++it) {
        if (it->clause == NULL) continue;
        ClauseSimp& c = *it;
        Clause& cl = *it->clause;
        
        s1.add(c);
        for (uint32_t j = 0; j < cl.size(); j++){
            if (ol_seen[cl[j].toInt()]) continue;
            ol_seen[cl[j].toInt()] = 1;
            
            vec<ClauseSimp>& n_occs = occur[(~cl[j]).toInt()];
            for (uint32_t k = 0; k < n_occs.size(); k++)
                if (n_occs[k].clause != c.clause && n_occs[k].clause->size() <= cl.size() && selfSubset(n_occs[k].clause->getAbst(), c.clause->getAbst()) && selfSubset(*n_occs[k].clause, cl, seen_tmp))
                    s1.add(n_occs[k]);
                
            vec<ClauseSimp>& p_occs = occur[cl[j].toInt()];
            for (uint32_t k = 0; k < p_occs.size(); k++)
                if (subsetAbst(p_occs[k].clause->getAbst(), c.clause->getAbst()))
                    s0.add(p_occs[k]);
        }
    }
    cl_added.clear();
    
    registerIteration(s0);
    registerIteration(s1);
    
    #ifdef BIT_MORE_VERBOSITY
    printf("c FIXED-POINT\n");
    #endif
    
    // Fixed-point for 1-subsumption:
    while (s1.size() > 0 || cl_touched.size() > 0){
        for (CSet::iterator it = cl_touched.begin(), end = cl_touched.end(); it != end; ++it) {
            if (it->clause != NULL) {
                s1.add(*it);
                s0.add(*it);
            }
        }
        
        cl_touched.clear();
        assert(solver.qhead == solver.trail.size());
        
        #ifdef BIT_MORE_VERBOSITY
        printf("c s1.size()=%d  cl_touched.size()=%d\n", s1.size(), cl_touched.size());
        #endif
        
        for (CSet::iterator it = s1.begin(), end = s1.end(); it != end; ++it) {
            if (numMaxSubsume1 == 0) break;
            if (it->clause != NULL) {
                subsume1(*it);
                numMaxSubsume1--;
                if (!solver.ok) return;
            }
        }
        s1.clear();
        
        if (!solver.ok) return;
        solver.ok = (solver.propagate().isNULL());
        if (!solver.ok){
            unregisterIteration(s1);
            unregisterIteration(s0);
            return; 
        }
        solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
    }
    unregisterIteration(s1);
    
    // Iteration pass for 0-subsumption:
    for (CSet::iterator it = s0.begin(), end = s0.end(); it != end; ++it) {
        if (it->clause != NULL) {
            subsume0(*it->clause, it->clause->getAbst());
            if (subsumedNonLearnt && it->clause->learnt()) it->clause->makeNonLearnt();
        }
    }
    s0.clear();
    unregisterIteration(s0);
}

ClauseSimp Subsumer::linkInClause(Clause& cl)
{
    ClauseSimp c(&cl, clauseID++);
    clauses.push(c);
    for (uint32_t i = 0; i < cl.size(); i++) {
        occur[cl[i].toInt()].push(c);
        touch(cl[i].var());
    }
    cl_added.add(c);
    
    return c;
}

void Subsumer::linkInAlreadyClause(ClauseSimp& c)
{
    Clause& cl = *c.clause;
    for (uint32_t i = 0; i < cl.size(); i++) {
        occur[cl[i].toInt()].push(c);
        touch(cl[i].var());
    }
}

template<bool UseCL>
void Subsumer::addFromSolver(vec<Clause*>& cs, bool alsoLearnt)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end = i + cs.size(); i !=  end; i++) {
        if (i+1 != end)
            __builtin_prefetch(*(i+1), 1, 1);

        if (!alsoLearnt && (*i)->learnt()) {
            *j++ = *i;
            (*i)->setUnsorted();
            continue;
        }

        if (!UseCL && (*i)->size() == 2) {
            //don't add binary clauses in this case
            *j++ = *i;
            (*i)->setUnsorted();
            continue;
        }

        ClauseSimp c(*i, clauseID++);
        clauses.push(c);
        Clause& cl = *c.clause;
        for (uint32_t i = 0; i < cl.size(); i++) {
            occur[cl[i].toInt()].push(c);
            touch(cl[i].var());
        }
        if (UseCL) {
            if (fullSubsume || cl.getVarChanged()) cl_added.add(c);
            else if (cl.getStrenghtened()) cl_touched.add(c);
        }

        if (!cl.learnt() && (cl.getVarChanged() || cl.getStrenghtened()))
            cl.calcAbstractionClause();
    }
    cs.shrink(i-j);
}

void Subsumer::freeMemory()
{
    for (uint32_t i = 0; i < occur.size(); i++) {
        occur[i].clear(true);
    }
}

void Subsumer::addBackToSolver()
{
    #ifdef HYPER_DEBUG2
    uint32_t binaryLearntAdded = 0;
    #endif

    assert(solver.clauses.size() == 0);
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause != NULL) {
            assert(clauses[i].clause->size() > 1);
            if (clauses[i].clause->size() == 2) {
                #ifdef HYPER_DEBUG2
                if (clauses[i].clause->learnt())
                    binaryLearntAdded++;
                #endif
                Clause* c = clauses[i].clause;
                if (!c->wasBin()) {
                    solver.detachClause(*c);
                    Clause *c2 = solver.clauseAllocator.Clause_new(*c);
                    solver.clauseAllocator.clauseFree(c);
                    solver.attachClause(*c2);
                    solver.becameBinary++;
                    c = c2;
                }
                solver.binaryClauses.push(c);
            } else {
                if (clauses[i].clause->learnt())
                    solver.learnts.push(clauses[i].clause);
                else
                    solver.clauses.push(clauses[i].clause);
            }
        }
    }
    
    #ifdef HYPER_DEBUG2
    std::cout << "Binary learnt added:" << binaryLearntAdded << std::endl;
    #endif
}

void Subsumer::removeWrong(vec<Clause*>& cs)
{
    Clause **i = cs.getData();
    Clause **j = i;
    for (Clause **end =  i + cs.size(); i != end; i++) {
        Clause& c = **i;
        if (!c.learnt())  {
            *j++ = *i;
            continue;
        }
        bool remove = false;
        for (Lit *l = c.getData(), *end2 = l+c.size(); l != end2; l++) {
            if (var_elimed[l->var()]) {
                remove = true;
                solver.detachClause(c);
                solver.clauseAllocator.clauseFree(&c);
                break;
            }
        }
        if (!remove)
            *j++ = *i;
    }
    cs.shrink(i-j);
}

void Subsumer::fillCannotEliminate()
{
    std::fill(cannot_eliminate.getData(), cannot_eliminate.getDataEnd(), false);
    for (uint32_t i = 0; i < solver.xorclauses.size(); i++) {
        const XorClause& c = *solver.xorclauses[i];
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    const vec<Clause*>& tmp = solver.varReplacer->getClauses();
    for (uint32_t i = 0; i < tmp.size(); i++) {
        const Clause& c = *tmp[i];
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            cannot_eliminate[c[i2].var()] = true;
    }
    
    #ifdef VERBOSE_DEBUG
    uint32_t tmpNum = 0;
    for (uint32_t i = 0; i < cannot_eliminate.size(); i++)
        if (cannot_eliminate[i])
            tmpNum++;
    std::cout << "Cannot eliminate num:" << tmpNum << std::endl;
    #endif
}

const bool Subsumer::subsumeWithBinaries(OnlyNonLearntBins* onlyNonLearntBins)
{
    clearAll();
    clauseID = 0;
    fullSubsume = true;
    addBinaryClauses.clear();

    //Clearing stats
    subsNonExistentumFailed = 0;
    clauses_subsumed = 0;
    literals_removed = 0;
    double myTime = cpuTime();
    uint32_t origTrailSize = solver.trail.size();

    clauses.reserve(solver.clauses.size());
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    addFromSolver<false>(solver.clauses);
    #ifdef DEBUG_BINARIES
    for (uint32_t i = 0; i < clauses.size(); i++) {
        assert(clauses[i].clause->size() != 2);
    }
    #endif //DEBUG_BINARIES

    numMaxSubsume0 = 300000 * (1+numCalls/2);
    numMaxSubsume1 = 10000 * (1+numCalls);

    for (uint32_t i = 0; i < solver.binaryClauses.size(); i++) {
        if (!solver.binaryClauses[i]->learnt() && numMaxSubsume0 > 0) {
            Clause& c = *solver.binaryClauses[i];
            subsume0(c, c.getAbst());
            numMaxSubsume0--;
        }
    }
    for (uint32_t i = 0; i < solver.binaryClauses.size(); i++) {
        if (numMaxSubsume1 > 0) {
            Clause& c = *solver.binaryClauses[i];
            subsume1Partial(c);
            if (!solver.ok) return false;
            numMaxSubsume1--;
        }
    }
    if (solver.verbosity >= 1) {
        std::cout << "c subs with bin: " << std::setw(8) << clauses_subsumed
        << "  lits-rem: " << std::setw(9) << literals_removed
        << "  v-fix: " << std::setw(4) <<solver.trail.size() - origTrailSize
        << "  time: " << std::setprecision(2) << std::setw(5) <<  cpuTime() - myTime << " s"
        << std::setw(17)  << "   |" << std::endl;
    }
    
    if (!subsWNonExistBinsFull(onlyNonLearntBins)) return false;

    #ifdef DEBUG_BINARIES
    for (uint32_t i = 0; i < clauses.size(); i++) {
        assert(clauses[i].clause == NULL || clauses[i].clause->size() != 2);
    }
    #endif //DEBUG_BINARIES
    addBackToSolver();
    for (uint32_t i = 0; i < addBinaryClauses.size(); i++) {
        Clause& c = *addBinaryClauses[i];
        solver.detachClause(c);
        Clause *c2 = solver.clauseAllocator.Clause_new(c);
        solver.clauseAllocator.clauseFree(&c);
        solver.attachClause(*c2);
        solver.becameBinary++;
        solver.binaryClauses.push(c2);
    }
    addBinaryClauses.clear();
    freeMemory();

    if (solver.verbosity >= 1) {
        std::cout << "c Subs w/ non-existent bins: " << std::setw(6) << subsNonExistentNum
        << " l-rem: " << std::setw(6) << subsNonExistentLitsRemoved
        << " v-fix: " << std::setw(5) << subsNonExistentumFailed
        << " done: " << std::setw(6) << doneNum
        << " time: " << std::fixed << std::setprecision(2) << std::setw(5) << subsNonExistentTime << " s"
        << std::setw(2)  << " |" << std::endl;
    }
    totalTime += cpuTime() - myTime;
    solver.order_heap.filter(Solver::VarFilter(solver));

    return true;
}

#define MAX_BINARY_PROP 40000000

const bool Subsumer::subsWNonExistBinsFull(OnlyNonLearntBins* onlyNonLearntBins)
{
    uint32_t oldClausesSubusmed = clauses_subsumed;
    uint32_t oldLitsRemoved = literals_removed;
    double myTime = cpuTime();
    uint64_t oldProps = solver.propagations;
    uint32_t oldTrailSize = solver.trail.size();
    uint64_t maxProp = MAX_BINARY_PROP;
    //if (!startUp) maxProp /= 3;
    if (clauses.size() > 2000000) maxProp /= 2;
    ps2.clear();
    ps2.growTo(2);
    toVisitAll.growTo(solver.nVars()*2, false);

    doneNum = 0;
    uint32_t startFrom = solver.mtrand.randInt(solver.order_heap.size());
    for (uint32_t i = 0; i < solver.order_heap.size(); i++) {
        Var var = solver.order_heap[(i+startFrom)%solver.order_heap.size()];
        if (solver.propagations - oldProps > maxProp) break;
        if (solver.assigns[var] != l_Undef || !solver.decision_var[var]) continue;
        doneNum++;

        Lit lit(var, true);
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) return false;
            continue;
        }

        //in the meantime it could have got assigned
        if (solver.assigns[var] != l_Undef) continue;
        lit = ~lit;
        if (!subsWNonExistBins(lit, onlyNonLearntBins)) {
            if (!solver.ok) return false;
            solver.cancelUntil(0);
            solver.uncheckedEnqueue(~lit);
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) return false;
            continue;
        }
    }
    subsNonExistentNum = clauses_subsumed - oldClausesSubusmed;
    subsNonExistentTime = cpuTime() - myTime;
    subsNonExistentumFailed = solver.trail.size() - oldTrailSize;
    subsNonExistentLitsRemoved = literals_removed - oldLitsRemoved;

    return true;
}

const bool Subsumer::subsWNonExistBins(const Lit& lit, OnlyNonLearntBins* onlyNonLearntBins)
{
    #ifdef VERBOSE_DEBUG
    std::cout << "subsWNonExistBins called with lit "; lit.print();
    std::cout << std::endl;
    #endif //VERBOSE_DEBUG
    toVisit.clear();
    solver.newDecisionLevel();
    solver.uncheckedEnqueueLight(lit);
    bool failed = !onlyNonLearntBins->propagate();
    if (failed) return false;

    assert(solver.decisionLevel() > 0);
    for (int c = solver.trail.size()-1; c > (int)solver.trail_lim[0]; c--) {
        Lit x = solver.trail[c];
        toVisit.push(x);
        toVisitAll[x.toInt()] = true;
    }
    solver.cancelUntil(0);

    if (toVisit.size() <= 1) {
        ps2[0] = ~lit;
        for (Lit *l = toVisit.getData(), *end = toVisit.getDataEnd(); l != end; l++) {
            ps2[1] = *l;
            assert(ps2[0] != ps2[1]);
            #ifdef VERBOSE_DEBUG
            std::cout << "Non-existent bin. lit1: "; ps2[0].print();
            std::cout << " lit2: "; ps2[1].print(); std::cout << std::endl;
            #endif //VERBOSE_DEBUG
            subsume0(ps2, calcAbstraction(ps2));
            subsume1Partial(ps2);
            if (!solver.ok) goto end;
        }
    } else {
        subsume0BIN(~lit, toVisitAll);
        if (!solver.ok) goto end;
    }

    end:
    for (uint32_t i = 0; i < toVisit.size(); i++)
        toVisitAll[toVisit[i].toInt()] = false;

    return solver.ok;
}

void Subsumer::clearAll()
{
    touched_list.clear();
    touched.clear();
    touched.growTo(solver.nVars(), false);
    for (Var var = 0; var < solver.nVars(); var++) {
        if (solver.decision_var[var] && solver.assigns[var] == l_Undef) touch(var);
        occur[2*var].clear();
        occur[2*var+1].clear();
    }
    clauses.clear();
    cl_added.clear();
    cl_touched.clear();
}

const bool Subsumer::simplifyBySubsumption(const bool alsoLearnt)
{
    if (solver.nClauses() > 20000000)  return true;
    
    double myTime = cpuTime();
    uint32_t origTrailSize = solver.trail.size();
    clauses_subsumed = 0;
    literals_removed = 0;
    numblockedClauseRemoved = 0;
    numCalls++;
    clauseID = 0;
    numVarsElimed = 0;
    blockTime = 0.0;
    clearAll();
    
    //if (solver.xorclauses.size() < 30000 && solver.clauses.size() < MAX_CLAUSENUM_XORFIND/10) addAllXorAsNorm();

    if (solver.performReplace && !solver.varReplacer->performReplace(true))
        return false;
    fillCannotEliminate();

    uint32_t expected_size;
    if (!alsoLearnt)
        expected_size = solver.clauses.size() + solver.binaryClauses.size();
    else
        expected_size = solver.clauses.size() + solver.binaryClauses.size() + solver.learnts.size();
    clauses.reserve(expected_size);
    cl_added.reserve(expected_size);
    cl_touched.reserve(expected_size);
    
    if (clauses.size() < 200000) fullSubsume = true;
    else fullSubsume = false;
    if (alsoLearnt) fullSubsume = true;

    //solver.clauseCleaner->cleanClauses(solver.learnts, ClauseCleaner::learnts);
    //addFromSolver<true>(solver.learnts, alsoLearnt);
    solver.clauseCleaner->cleanClauses(solver.clauses, ClauseCleaner::clauses);
    addFromSolver<true>(solver.clauses, alsoLearnt);

    //It is IMPERATIVE to add binaryClauses last. The non-binary clauses can
    //move to binaryClauses during cleaning!!!!
    solver.clauseCleaner->removeSatisfied(solver.binaryClauses, ClauseCleaner::binaryClauses);
    addFromSolver<true>(solver.binaryClauses, alsoLearnt);
    
    //Limits
    if (clauses.size() > 3500000) {
        numMaxSubsume0 = 900000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 5.0 * (0.8+(double)(numCalls)/4.0));
        numMaxSubsume1 = 100000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(30000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (clauses.size() <= 3500000 && clauses.size() > 1500000) {
        numMaxSubsume0 = 2000000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 2.0 * (0.8+(double)(numCalls)/4.0));
        numMaxSubsume1 = 300000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(50000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (clauses.size() <= 1500000) {
        numMaxSubsume0 = 4000000 * (1+numCalls/2);
        numMaxElim = (uint32_t)((double)solver.order_heap.size() / 2.0 * (0.8+(double)(numCalls)/2.0));
        numMaxSubsume1 = 400000 * (1+numCalls/2);
        numMaxBlockToVisit = (int64_t)(80000.0 * (0.8+(double)(numCalls)/3.0));
    }
    if (solver.order_heap.size() > 200000)
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 3.5 * (0.8+(double)(numCalls)/4.0));
    else
        numMaxBlockVars = (uint32_t)((double)solver.order_heap.size() / 1.5 * (0.8+(double)(numCalls)/4.0));

    if (numCalls == 1) numMaxSubsume1 = 0;
    if (!solver.doSubsume1) numMaxSubsume1 = 0;
    if (alsoLearnt) {
        numMaxElim = 0;
        numMaxSubsume1 = 0;
        numMaxBlockVars = 0;
        numMaxBlockToVisit = 0;
        fullSubsume = true;
    }
    
    //For debugging
    //numMaxBlockToVisit = std::numeric_limits<int64_t>::max();
    //numMaxElim = std::numeric_limits<uint32_t>::max();
    //numMaxSubsume0 = std::numeric_limits<uint32_t>::max();
    //numMaxSubsume1 = std::numeric_limits<uint32_t>::max();
    //numMaxBlockVars = std::numeric_limits<uint32_t>::max();
    
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  num clauses:" << clauses.size() << std::endl;
    std::cout << "c  time to link in:" << cpuTime()-myTime << std::endl;
    #endif
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (numMaxSubsume0 == 0) break;
        if (clauses[i].clause != NULL && 
            (fullSubsume
            || !clauses[i].clause->subsume0IsFinished())
            )
        {
            subsume0(*clauses[i].clause, clauses[i].clause->getAbst());
            if (subsumedNonLearnt && clauses[i].clause->learnt()) clauses[i].clause->makeNonLearnt();
            numMaxSubsume0--;
        }
    }
    
    origNClauses = clauses.size();
    
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  time until pre-subsume0 clauses and subsume1 2-learnts:" << cpuTime()-myTime << std::endl;
    #endif
    
    if (!solver.ok) return false;
    #ifdef VERBOSE_DEBUG
    std::cout << "c   pre-subsumed:" << clauses_subsumed << std::endl;
    std::cout << "c   cl_added:" << cl_added.size() << std::endl;
    std::cout << "c   cl_touched:" << cl_touched.size() << std::endl;
    std::cout << "c   clauses:" << clauses.size() << std::endl;
    std::cout << "c   origNClauses:" << origNClauses << std::endl;
    #endif
    
    if (clauses.size() > 10000000)  goto endSimplifyBySubsumption;
    if (solver.doBlockedClause && numCalls % 3 == 1) blockedClauseRemoval();
    do{
        #ifdef BIT_MORE_VERBOSITY
        std::cout << "c time before the start of almost_all/smaller: " << cpuTime() - myTime << std::endl;
        #endif
        if (numMaxSubsume0 > 0) {
            if (cl_added.size() > origNClauses / 2) {
                almost_all_database();
                if (!solver.ok) return false;
            } else {
                smaller_database();
                if (!solver.ok) return false;
            }
        }
        cl_added.clear();
        assert(cl_added.size() == 0);
        assert(solver.ok);
        solver.ok = (solver.propagate().isNULL());
        if (!solver.ok) {
            return false;
        }
        solver.clauseCleaner->cleanClausesBewareNULL(clauses, ClauseCleaner::simpClauses, *this);
        
        #ifdef BIT_MORE_VERBOSITY
        std::cout << "c time until the end of almost_all/smaller: " << cpuTime() - myTime << std::endl;
        #endif
        
        if (!solver.doVarElim) break;
        
        #ifdef BIT_MORE_VERBOSITY
        printf("c VARIABLE ELIMINIATION\n");
        std::cout << "c  toucheds list size:" << touched_list.size() << std::endl;
        #endif
        vec<Var> init_order;
        orderVarsForElim(init_order);   // (will untouch all variables)
        
        for (bool first = true; numMaxElim > 0; first = false){
            uint32_t vars_elimed = 0;
            vec<Var> order;
            
            if (first) {
                //init_order.copyTo(order);
                for (uint32_t i = 0; i < init_order.size(); i++) {
                    const Var var = init_order[i];
                    if (!cannot_eliminate[var] && solver.decision_var[var])
                        order.push(var);
                }
            } else {
                for (uint32_t i = 0; i < touched_list.size(); i++) {
                    const Var var = touched_list[i];
                    if (!cannot_eliminate[var] && solver.decision_var[var])
                        order.push(var);
                    touched[var] = false;
                }
                touched_list.clear();
            }
            #ifdef VERBOSE_DEBUG
            std::cout << "Order size:" << order.size() << std::endl;
            #endif
            
            assert(solver.qhead == solver.trail.size());
            for (uint32_t i = 0; i < order.size() && numMaxElim > 0; i++, numMaxElim--) {
                if (maybeEliminate(order[i])) {
                    if (!solver.ok) {
                        return false;
                    }
                    vars_elimed++;
                }
            }
            assert(solver.qhead == solver.trail.size());
            
            if (vars_elimed == 0) break;
            
            numVarsElimed += vars_elimed;
            #ifdef BIT_MORE_VERBOSITY
            printf("c  #var-elim: %d\n", vars_elimed);
            std::cout << "c time until the end of varelim: " << cpuTime() - myTime << std::endl;
            #endif
        }
    }while (cl_added.size() > 100 && numMaxElim > 0);
    endSimplifyBySubsumption:
    
    if (!solver.ok) return false;
    solver.ok = (solver.propagate().isNULL());
    if (!solver.ok) {
        return false;
    }
    
    #ifndef NDEBUG
    verifyIntegrity();
    #endif

    removeWrong(solver.learnts);
    removeWrong(solver.binaryClauses);
    removeAssignedVarsFromEliminated();

    solver.order_heap.filter(Solver::VarFilter(solver));
    
    addBackToSolver();
    freeMemory();
    
    if (solver.verbosity >= 1) {
        std::cout << "c |  lits-rem: " << std::setw(9) << literals_removed
        << "  cl-subs: " << std::setw(8) << clauses_subsumed
        << "  v-elim: " << std::setw(6) << numVarsElimed
        << "  v-fix: " << std::setw(4) <<solver.trail.size() - origTrailSize
        << "  time: " << std::setprecision(2) << std::setw(5) << (cpuTime() - myTime) << " s"
        //<< " blkClRem: " << std::setw(5) << numblockedClauseRemoved
        << "   |" << std::endl;
        
        if (numblockedClauseRemoved > 0 || blockTime > 0.0) {
            std::cout 
            << "c |  Blocked clauses removed: " << std::setw(8) << numblockedClauseRemoved 
            << "    Time: " << std::fixed << std::setprecision(2) << std::setw(4) << blockTime << " s" 
            << "                                    |" << std::endl;
        }
    }
    totalTime += cpuTime() - myTime;

    solver.testAllClauseAttach();
    return true;
}

void Subsumer::removeAssignedVarsFromEliminated()
{
    for (Var var = 0; var < var_elimed.size(); var++) {
        if (var_elimed[var] && solver.assigns[var] != l_Undef) {
            var_elimed[var] = false;
            solver.setDecisionVar(var, true);
            numElimed--;
            map<Var, vector<Clause*> >::iterator it = elimedOutVar.find(var);
            if (it != elimedOutVar.end()) {
                //TODO memory loss here
                elimedOutVar.erase(it);
            }
        }
    }
}

template<class T>
void Subsumer::findSubsumed(const T& ps, uint32_t abs, vec<ClauseSimp>& out_subsumed)
{
    #ifdef VERBOSE_DEBUG
    cout << "findSubsumed: ";
    for (uint32_t i = 0; i < ps.size(); i++) {
        if (ps[i].sign()) printf("-");
        printf("%d ", ps[i].var() + 1);
    }
    printf("0\n");
    #endif
    
    uint32_t min_i = 0;
    for (uint32_t i = 1; i < ps.size(); i++){
        if (occur[ps[i].toInt()].size() < occur[ps[min_i].toInt()].size())
            min_i = i;
    }
    
    vec<ClauseSimp>& cs = occur[ps[min_i].toInt()];
    for (ClauseSimp *it = cs.getData(), *end = it + cs.size(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        if (it->clause != (Clause*)&ps && subsetAbst(abs, it->clause->getAbst()) && ps.size() <= it->clause->size() && subset(ps, *it->clause)) {
            out_subsumed.push(*it);
            #ifdef VERBOSE_DEBUG
            cout << "subsumed: ";
            it->clause->plainPrint();
            #endif
        }
    }
}

void inline Subsumer::MigrateToPsNs(vec<ClauseSimp>& poss, vec<ClauseSimp>& negs, vec<ClauseSimp>& ps, vec<ClauseSimp>& ns, const Var x)
{
    poss.moveTo(ps);
    negs.moveTo(ns);
    
    for (uint32_t i = 0; i < ps.size(); i++)
        unlinkClause(ps[i], x);
    for (uint32_t i = 0; i < ns.size(); i++)
        unlinkClause(ns[i], x);
}

void inline Subsumer::DeallocPsNs(vec<ClauseSimp>& ps, vec<ClauseSimp>& ns)
{
    for (uint32_t i = 0; i < ps.size(); i++) {
        //clauses[ps[i].index].clause = NULL;
        //clauseFree(ps[i].clause);
    }
    for (uint32_t i = 0; i < ns.size(); i++) {
        //clauses[ns[i].index].clause = NULL;
        //clauseFree(ns[i].clause);
    }
}

// Returns TRUE if variable was eliminated.
bool Subsumer::maybeEliminate(const Var x)
{
    assert(solver.qhead == solver.trail.size());
    assert(!var_elimed[x]);
    assert(!cannot_eliminate[x]);
    assert(solver.decision_var[x]);
    if (solver.value(x) != l_Undef) return false;
    if (occur[Lit(x, false).toInt()].size() == 0 && occur[Lit(x, true).toInt()].size() == 0)
        return false;
    
    vec<ClauseSimp>&   poss = occur[Lit(x, false).toInt()];
    vec<ClauseSimp>&   negs = occur[Lit(x, true).toInt()];
    
    // Heuristic CUT OFF:
    if (poss.size() >= 10 && negs.size() >= 10)
        return false;
    
    // Count clauses/literals before elimination:
    int before_clauses  = poss.size() + negs.size();
    uint32_t before_literals = 0;
    for (uint32_t i = 0; i < poss.size(); i++) before_literals += poss[i].clause->size();
    for (uint32_t i = 0; i < negs.size(); i++) before_literals += negs[i].clause->size();
    
    // Heuristic CUT OFF2:
    if ((poss.size() >= 3 && negs.size() >= 3 && before_literals > 300)
        && clauses.size() > 1500000)
        return false;
    if ((poss.size() >= 5 && negs.size() >= 5 && before_literals > 400)
        && clauses.size() <= 1500000 && clauses.size() > 200000)
        return false;
    if ((poss.size() >= 8 && negs.size() >= 8 && before_literals > 700)
        && clauses.size() <= 200000)
        return false;
    
    // Count clauses/literals after elimination:
    int after_clauses  = 0;
    vec<Lit>  dummy;
    for (uint32_t i = 0; i < poss.size(); i++) for (uint32_t j = 0; j < negs.size(); j++){
        // Merge clauses. If 'y' and '~y' exist, clause will not be created.
        dummy.clear();
        bool ok = merge(*poss[i].clause, *negs[j].clause, Lit(x, false), Lit(x, true), dummy);
        if (ok){
            after_clauses++;
            if (after_clauses > before_clauses) goto Abort;
        }
    }
    Abort:;
    
    //Eliminate:
    if (after_clauses  <= before_clauses) {
        vec<ClauseSimp> ps, ns;
        MigrateToPsNs(poss, negs, ps, ns, x);
        for (uint32_t i = 0; i < ps.size(); i++) for (uint32_t j = 0; j < ns.size(); j++){
            dummy.clear();
            bool ok = merge(*ps[i].clause, *ns[j].clause, Lit(x, false), Lit(x, true), dummy);
            if (ok){
                uint32_t group_num = 0;
                #ifdef STATS_NEEDED
                group_num = solver.learnt_clause_group++;
                if (solver.dynamic_behaviour_analysis) {
                    string name = solver.logger.get_group_name(ps[i].clause->getGroup()) + " " + solver.logger.get_group_name(ns[j].clause->getGroup());
                    solver.logger.set_group_name(group_num, name);
                }
                #endif
                Clause* cl = solver.addClauseInt(dummy, group_num);
                if (cl != NULL) {
                    ClauseSimp c = linkInClause(*cl);
                    subsume0(*cl, cl->getAbst());
                }
                if (!solver.ok) return true;
            }
        }
        DeallocPsNs(ps, ns);
        goto Eliminated;
    }
    
    return false;
    
    Eliminated:
    assert(occur[Lit(x, false).toInt()].size() + occur[Lit(x, true).toInt()].size() == 0);
    var_elimed[x] = true;
    numElimed++;
    solver.setDecisionVar(x, false);
    return true;
}

// Returns FALSE if clause is always satisfied ('out_clause' should not be used). 'seen' is assumed to be cleared.
bool Subsumer::merge(const Clause& ps, const Clause& qs, const Lit without_p, const Lit without_q, vec<Lit>& out_clause)
{
    for (uint32_t i = 0; i < ps.size(); i++){
        if (ps[i] != without_p){
            seen_tmp[ps[i].toInt()] = 1;
            out_clause.push(ps[i]);
        }
    }
    
    for (uint32_t i = 0; i < qs.size(); i++){
        if (qs[i] != without_q){
            if (seen_tmp[(~qs[i]).toInt()]){
                for (uint32_t i = 0; i < ps.size(); i++)
                    seen_tmp[ps[i].toInt()] = 0;
                return false;
            }
            if (!seen_tmp[qs[i].toInt()])
                out_clause.push(qs[i]);
        }
    }
    
    for (uint32_t i = 0; i < ps.size(); i++)
        seen_tmp[ps[i].toInt()] = 0;
    
    return true;
}

struct myComp {
    bool operator () (const pair<int, Var>& x, const pair<int, Var>& y) {
        return x.first < y.first ||
            (!(y.first < x.first) && x.second < y.second);
    }
};
    
// Side-effect: Will untouch all variables.
void Subsumer::orderVarsForElim(vec<Var>& order)
{
    order.clear();
    vec<pair<int, Var> > cost_var;
    for (uint32_t i = 0; i < touched_list.size(); i++){
        Var x = touched_list[i];
        touched[x] = 0;
        cost_var.push(std::make_pair( occur[Lit(x, false).toInt()].size() * occur[Lit(x, true).toInt()].size() , x ));
    }
    
    touched_list.clear();
    std::sort(cost_var.getData(), cost_var.getData()+cost_var.size(), myComp());
    
    for (uint32_t x = 0; x < cost_var.size(); x++) {
        if (cost_var[x].first != 0)
            order.push(cost_var[x].second);
    }
}

void Subsumer::verifyIntegrity()
{
    vector<uint> occurNum(solver.nVars()*2, 0);
    
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i].clause == NULL) continue;
        Clause& c = *clauses[i].clause;
        for (uint32_t i2 = 0; i2 < c.size(); i2++)
            occurNum[c[i2].toInt()]++;
    }
    
    for (uint32_t i = 0; i < occurNum.size(); i++) {
        assert(occurNum[i] == occur[i].size());
    }
}

const bool Subsumer::allTautology(const vec<Lit>& ps, const Lit lit)
{
    #ifdef VERBOSE_DEBUG
    cout << "allTautology: ";
    for (uint32_t i = 0; i < ps.size(); i++) {
        if (ps[i].sign()) printf("-");
        printf("%d ", ps[i].var() + 1);
    }
    printf("0\n");
    #endif
    
    vec<ClauseSimp>& cs = occur[lit.toInt()];
    if (cs.size() == 0) return true;
    
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        seen_tmp[l->toInt()] = true;
    }
    
    bool allIsTautology = true;
    for (ClauseSimp *it = cs.getData(), *end = cs.getDataEnd(); it != end; it++){
        if (it+1 != end)
            __builtin_prefetch((it+1)->clause, 1, 1);
        
        Clause& c = *it->clause;
        for (Lit *l = c.getData(), *end2 = l + c.size(); l != end2; l++) {
            if (*l != lit && seen_tmp[(~(*l)).toInt()]) {
                goto next;
            }
        }
        allIsTautology = false;
        break;
        
        next:;
    }
    
    for (const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        seen_tmp[l->toInt()] = false;
    }
    
    return allIsTautology;
}

void Subsumer::blockedClauseRemoval()
{
    if (numMaxBlockToVisit < 0) return;
    if (solver.order_heap.size() < 1) return;
    double myTime = cpuTime();
    vec<ClauseSimp> toRemove;
    
    touchedBlockedVars = priority_queue<VarOcc, vector<VarOcc>, MyComp>();
    touchedBlockedVarsBool.clear();
    touchedBlockedVarsBool.growTo(solver.nVars(), false);
    for (uint32_t i =  0; i < solver.order_heap.size() && i < numMaxBlockVars; i++) {
        touchBlockedVar(solver.order_heap[solver.mtrand.randInt(solver.order_heap.size()-1)]);
    }
    
    while (touchedBlockedVars.size() > 100  && numMaxBlockToVisit > 0) {
        VarOcc vo = touchedBlockedVars.top();
        touchedBlockedVars.pop();
        
        if (solver.assigns[vo.var] != l_Undef || !solver.decision_var[vo.var] || cannot_eliminate[vo.var])
            continue;
        touchedBlockedVarsBool[vo.var] = false;
        Lit lit = Lit(vo.var, false);
        Lit negLit = Lit(vo.var, true);
        
        numMaxBlockToVisit -= (int64_t)occur[lit.toInt()].size();
        numMaxBlockToVisit -= (int64_t)occur[negLit.toInt()].size();
        //if (!tryOneSetting(lit, negLit)) {
            tryOneSetting(negLit, lit);
       // }
    }
    blockTime += cpuTime() - myTime;
    
    #ifdef BIT_MORE_VERBOSITY
    std::cout << "c  Total fime for block until now: " << blockTime << std::endl;
    #endif
}

const bool Subsumer::tryOneSetting(const Lit lit, const Lit negLit)
{
    uint32_t toRemove = 0;
    bool returnVal = false;
    vec<Lit> cl;
    
    for(ClauseSimp *it = occur[lit.toInt()].getData(), *end = occur[lit.toInt()].getDataEnd(); it != end; it++) {
        cl.clear();
        cl.growTo(it->clause->size()-1);
        for (uint32_t i = 0, i2 = 0; i < it->clause->size(); i++) {
            if ((*it->clause)[i] != lit) {
                cl[i2] = (*it->clause)[i];
                i2++;
            }
        }
        
        if (allTautology(cl, negLit)) {
            toRemove++;
        } else {
            break;
        }
    }
    
    if (toRemove == occur[lit.toInt()].size()) {
        var_elimed[lit.var()] = true;
        solver.setDecisionVar(lit.var(), false);
        vec<ClauseSimp> toRemove(occur[lit.toInt()]);
        for (ClauseSimp *it = toRemove.getData(), *end = toRemove.getDataEnd(); it != end; it++) {
            #ifdef VERBOSE_DEBUG
            std::cout << "Next varelim because of block clause elim" << std::endl;
            #endif //VERBOSE_DEBUG
            unlinkClause(*it, lit.var());
            numblockedClauseRemoved++;
        }
        
        vec<ClauseSimp> toRemove2(occur[negLit.toInt()]);
        for (ClauseSimp *it = toRemove2.getData(), *end = toRemove2.getDataEnd(); it != end; it++) {
            #ifdef VERBOSE_DEBUG
            std::cout << "Next varelim because of block clause elim" << std::endl;
            #endif //VERBOSE_DEBUG
            unlinkClause(*it, lit.var());
            numblockedClauseRemoved++;
        }
        returnVal = true;
    }
    
    return returnVal;
}

const bool Subsumer::checkElimedUnassigned() const
{
    for (uint32_t i = 0; i < var_elimed.size(); i++) {
        if (var_elimed[i]) {
            assert(solver.assigns[i] == l_Undef);
            if (solver.assigns[i] != l_Undef) return false;
        }
    }

    return true;
}

/*
int hash32shift(int key)
{
    key = ~key + (key << 15); // key = (key << 15) - key - 1;
    key = key ^ (key >> 12);
    key = key + (key << 2);
    key = key ^ (key >> 4);
    key = key * 2057; // key = (key + (key << 3)) + (key << 11);
    key = key ^ (key >> 16);
    return key;
}

vector<char> Subsumer::merge()
{
    vector<char> var_merged(solver.nVars(), false);
    double myTime = cpuTime();
    
    vector<varDataStruct> varData(solver.nVars());
    
    for (Var var = 0; var < solver.nVars(); var++) if (solver.decision_var[var] && solver.assigns[var] == l_Undef && !cannot_eliminate[var]) {
        varDataStruct thisVar;
        
        vec<ClauseSimp>& toCountPos = occur[Lit(var, false).toInt()];
        thisVar.numPosClauses = toCountPos.size();
        for (uint32_t i2 = 0; i2 < toCountPos.size(); i2++) {
            thisVar.sumPosClauseSize += toCountPos[i2].clause->size();
            for (Lit *l = toCountPos[i2].clause->getData(), *end = l + toCountPos[i2].clause->size(); l != end; l++) {
                if (l->var() != var) thisVar.posHash ^= hash32shift(l->toInt());
            }
        }
        
        vec<ClauseSimp>& toCountNeg = occur[Lit(var, true).toInt()];
        thisVar.numNegClauses = toCountNeg.size();
        for (uint32_t i2 = 0; i2 < toCountNeg.size(); i2++) {
            thisVar.sumNegClauseSize += toCountNeg[i2].clause->size();
            for (Lit *l = toCountNeg[i2].clause->getData(), *end = l + toCountNeg[i2].clause->size(); l != end; l++) {
                if (l->var() != var) thisVar.negHash ^= hash32shift(l->toInt());
            }
        }
        
        varData[var] = thisVar;
    }
    
    map<varDataStruct, vector<Var> > dataToVar;
    for (Var var = 0; var < solver.nVars(); var++) if (solver.decision_var[var] && solver.assigns[var] == l_Undef) {
        dataToVar[varData[var]].push_back(var);
        assert(dataToVar[varData[var]].size() > 0);
    }
    
    for (map<varDataStruct, vector<Var> >::iterator it = dataToVar.begin(); it != dataToVar.end(); it++) {
        //std::cout << "size: " << it->second.size() << std::endl;
        for (uint i = 0; i < it->second.size()-1; i++) {
            assert(it->second.size() > i+1);
            assert(varData[it->second[i]] == varData[it->second[i+1]]);
        }
    }
    
    uint64_t checked = 0;
    uint64_t replaced = 0;
    for (Var var = 0; var < solver.nVars(); var++) if (solver.decision_var[var] && solver.assigns[var] == l_Undef && !cannot_eliminate[var]) {
        varDataStruct tmp = varData[var];
        assert(dataToVar[tmp].size() > 0);
        
        if (dataToVar[tmp].size() > 0) {
            map<varDataStruct, vector<Var> >::iterator it = dataToVar.find(tmp);
            for (uint i = 0; i < it->second.size(); i++) if (it->second[i] != var) {
                checked ++;
                if (checkIfSame(Lit(var, false), Lit(it->second[i], false)) &&
                    (checkIfSame(Lit(var, true), Lit(it->second[i], true))))
                {
                    vec<Lit> ps(2);
                    ps[0] = Lit(var, false);
                    ps[1] = Lit(it->second[i], false);
                    solver.varReplacer->replace(ps, true, 0);
                    replaced++;
                    goto next;
                    
                }
            }
        }
        
        tmp.reversePolarity();
        if (dataToVar[tmp].size() > 0) {
            map<varDataStruct, vector<Var> >::iterator it = dataToVar.find(tmp);
            for (uint i = 0; i < it->second.size(); i++) if (it->second[i] != var) {
                checked ++;
                if (checkIfSame(Lit(var, true), Lit(it->second[i], false)) &&
                    (checkIfSame(Lit(var, false), Lit(it->second[i], true))))
                {
                    vec<Lit> ps(2);
                    ps[0] = Lit(var, false);
                    ps[1] = Lit(it->second[i], false);
                    solver.varReplacer->replace(ps, false, 0);
                    replaced++;
                    goto next;
                }
            }
        }
        
        next:;
    }
        
    std::cout << "c |  Merging vars in same clauses.  checked: " << std::setw(5) << checked << " replaced: " << std::setw(5) << replaced << " time: " << std::setprecision(2) << std::setw(5) << cpuTime()-myTime << std::endl;
    
    return var_merged;
}*/

/*const bool Subsumer::checkIfSame(const Lit lit1, const Lit lit2)
{
    assert(lit1.var() != lit2.var());
    #ifdef VERBOSE_DEBUG
    std::cout << "checking : " << lit1.var()+1 << " , " << lit2.var()+1 << std::endl;
    #endif
    
    vec<ClauseSimp>& occSet1 = occur[lit1.toInt()];
    vec<ClauseSimp>& occSet2 = occur[lit2.toInt()];
    vec<Lit> tmp;
    
    for (ClauseSimp *it = occSet1.getData(), *end = it + occSet1.size(); it != end; it++) {
        bool found = false;
        tmp.clear();
        uint32_t clauseSize = it->clause->size();
        
        for (Lit *l = it->clause->getData(), *end2 = l + it->clause->size(); l != end2; l++) {
            if (l->var() != lit1.var()) {
                tmp.push(*l);
                seen_tmp[l->toInt()] = true;
            }
        }
        #ifdef VERBOSE_DEBUG
        std::cout << "orig: ";
        it->clause->plainPrint();
        #endif
        
        for (ClauseSimp *it2 = occSet2.getData(), *end2 = it2 + occSet2.size(); (it2 != end2 && !found); it2++) {
            if (it2->clause->size() != clauseSize) continue;
            
            for (Lit *l = it2->clause->getData(), *end3 = l + tmp.size(); l != end3; l++) if (l->var() != lit1.var()) {
                if (!seen_tmp[l->toInt()]) goto next;
            }
            found = true;
            
            #ifdef VERBOSE_DEBUG
            std::cout << "OK:   ";
            it2->clause->plainPrint();
            #endif
            next:;
        }
        
        for (Lit *l = tmp.getData(), *end2 = l + tmp.size(); l != end2; l++) {
            seen_tmp[l->toInt()] = false;
        }
        
        if (!found) return false;
    }
    #ifdef VERBOSE_DEBUG
    std::cout << "OK" << std::endl;
    #endif
    
    return true;
}*/

}; //NAMESPACE MINISAT
