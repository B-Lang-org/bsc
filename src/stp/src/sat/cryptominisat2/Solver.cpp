/****************************************************************************************[Solver.C]
MiniSat -- Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
CryptoMiniSat -- Copyright (c) 2009 Mate Soos
glucose -- Gilles Audemard, Laurent Simon (2008)

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include "Solver.h"
#include <cmath>
#include <string.h>
#include <algorithm>
#include <limits.h>
#include <vector>
#include <iomanip>

#include "Clause.h"
#include "time_mem.h"

#include "VarReplacer.h"
#include "FindUndef.h"
#include "XorFinder.h"
#include "ClauseCleaner.h"
#include "RestartTypeChooser.h"
#include "FailedVarSearcher.h"
#include "Subsumer.h"
#include "PartHandler.h"
#include "XorSubsumer.h"
#include "StateSaver.h"
#include "UselessBinRemover.h"
#include "OnlyNonLearntBins.h"

#ifdef USE_GAUSS
#include "Gaussian.h"
#include "MatrixFinder.h"
#endif //USE_GAUSS

#ifdef _MSC_VER
#define __builtin_prefetch(a,b,c)
//#define __builtin_prefetch(a,b)
#endif //_MSC_VER

//#define DEBUG_UNCHECKEDENQUEUE_LEVEL0
//#define VERBOSE_DEBUG_POLARITIES
//#define DEBUG_DYNAMIC_RESTART

namespace MINISAT
{
using namespace MINISAT;

//=================================================================================================
// Constructor/Destructor:


Solver::Solver() :
        // Parameters: (formerly in 'SearchParams')
        random_var_freq(0.02)
        , clause_decay (1 / 0.999)
        , restart_first(100), restart_inc(1.5), learntsize_factor((double)1/(double)3), learntsize_inc(1)

        // More parameters:
        //
        , expensive_ccmin  (true)
        , polarity_mode    (polarity_auto)
        , verbosity        (0)
        , restrictedPickBranch(0)
        , findNormalXors   (true)
        , findBinaryXors   (true)
        , regularlyFindBinaryXors(true)
        , performReplace   (true)
        , conglomerateXors (true)
        , heuleProcess     (true)
        , schedSimplification(true)
        , doSubsumption    (true)
        , doXorSubsumption (true)
        , doPartHandler    (true)
        , doHyperBinRes    (true)
        , doBlockedClause  (true)
        , doVarElim        (true)
        , doSubsume1       (true)
        , failedVarSearch  (true)
        , addExtraBins     (true)
        , removeUselessBins(true)
        , regularRemoveUselessBins(true)
        , subsumeWithNonExistBinaries(true)
        , regularSubsumeWithNonExistBinaries(true)
        , libraryUsage     (true)
        , greedyUnbound    (false)
        , fixRestartType   (auto_restart)

        // Statistics: (formerly in 'SolverStats')
        //
        , starts(0), dynStarts(0), staticStarts(0), fullStarts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
        , clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)
        , nbDL2(0), nbBin(0), lastNbBin(0), becameBinary(0), lastSearchForBinaryXor(0), nbReduceDB(0)
        , improvedClauseNo(0), improvedClauseSize(0)
        
        #ifdef USE_GAUSS
        , sum_gauss_called (0)
        , sum_gauss_confl  (0)
        , sum_gauss_prop   (0)
        , sum_gauss_unit_truths (0)
        #endif //USE_GAUSS
        , ok               (true)
        , var_inc          (128)
        , cla_inc          (1)
        
        , curRestart       (1)
        , nbclausesbeforereduce (NBCLAUSESBEFOREREDUCE)
        , nbCompensateSubsumer (0)
        
        , qhead            (0)
        , simpDB_assigns   (-1)
        , simpDB_props     (0)
        , order_heap       (VarOrderLt(activity))
        , progress_estimate(0)
        , remove_satisfied (true)
        , mtrand((unsigned long int)0)
        , restartType      (static_restart)
        , lastSelectedRestartType (static_restart)
        #ifdef STATS_NEEDED
        , logger(verbosity)
        , dynamic_behaviour_analysis(false) //do not document the proof as default
        #endif
        , maxRestarts(UINT_MAX)
        , MYFLAG           (0)
        , learnt_clause_group(0)
        , libraryCNFFile   (NULL)
        , simplifying      (false)
{
    varReplacer = new VarReplacer(*this);
    clauseCleaner = new ClauseCleaner(*this);
    failedVarSearcher = new FailedVarSearcher(*this);
    partHandler = new PartHandler(*this);
    subsumer = new Subsumer(*this);
    xorSubsumer = new XorSubsumer(*this);
    restartTypeChooser = new RestartTypeChooser(*this);
    #ifdef USE_GAUSS
    matrixFinder = new MatrixFinder(*this);
    #endif //USE_GAUSS
    
    #ifdef STATS_NEEDED
    logger.setSolver(this);
    #endif
}

Solver::~Solver()
{
    #ifdef USE_GAUSS
    clearGaussMatrixes();
    delete matrixFinder;
    #endif
    
    delete varReplacer;
    delete clauseCleaner;
    delete failedVarSearcher;
    delete partHandler;
    delete subsumer;
    delete xorSubsumer;
    delete restartTypeChooser;
    
    if (libraryCNFFile)
        fclose(libraryCNFFile);
}

//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision_var' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
Var Solver::newVar(bool dvar)
{
    Var v = nVars();
    watches   .push();          // (list for positive literal)
    watches   .push();          // (list for negative literal)
    binwatches.push();          // (list for positive literal)
    binwatches.push();          // (list for negative literal)
    xorwatches.push();          // (list for variables in xors)
    reason    .push(PropagatedFrom());
    assigns   .push(l_Undef);
    level     .push(-1);
    activity  .push(0);
    seen      .push_back(0);
    seen      .push_back(0);
    permDiff  .push(0);
    
    polarity  .push_back(defaultPolarity());
    #ifdef USE_OLD_POLARITIES
    oldPolarity.push_back(defaultPolarity());
    #endif //USE_OLD_POLARITIES

    decision_var.push_back(dvar);
    insertVarOrder(v);
    
    varReplacer->newVar();
    if (doPartHandler) partHandler->newVar();
    if (doSubsumption || subsumeWithNonExistBinaries || regularSubsumeWithNonExistBinaries) subsumer->newVar();
    if (doXorSubsumption) xorSubsumer->newVar();

    insertVarOrder(v);
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis)
        logger.new_var(v);
    #endif
    
    if (libraryCNFFile)
        fprintf(libraryCNFFile, "c Solver::newVar() called\n");

    return v;
}

template<class T>
XorClause* Solver::addXorClauseInt(T& ps, bool xor_clause_inverted, const uint32_t group)
{
    assert(qhead == trail.size());
    assert(decisionLevel() == 0);
    
    if (ps.size() > (0x01UL << 18)) {
        std::cout << "Too long clause!" << std::endl;
        exit(-1);
    }
    std::sort(ps.getData(), ps.getDataEnd());
    Lit p;
    uint32_t i, j;
    for (i = j = 0, p = lit_Undef; i != ps.size(); i++) {
        if (ps[i].var() == p.var()) {
            //added, but easily removed
            j--;
            p = lit_Undef;
            if (!assigns[ps[i].var()].isUndef())
                xor_clause_inverted ^= assigns[ps[i].var()].getBool();
        } else if (assigns[ps[i].var()].isUndef()) //just add
            ps[j++] = p = ps[i];
        else //modify xor_clause_inverted instead of adding
            xor_clause_inverted ^= (assigns[ps[i].var()].getBool());
    }
    ps.shrink(i - j);
    
    switch(ps.size()) {
        case 0: {
            if (!xor_clause_inverted) ok = false;
            return NULL;
        }
        case 1: {
            uncheckedEnqueue(Lit(ps[0].var(), xor_clause_inverted));
            ok = (propagate().isNULL());
            return NULL;
        }
        case 2: {
            #ifdef VERBOSE_DEBUG
            cout << "--> xor is 2-long, replacing var " << ps[0].var()+1 << " with " << (!xor_clause_inverted ? "-" : "") << ps[1].var()+1 << endl;
            #endif

            ps[0] = ps[0].unsign();
            ps[1] = ps[1].unsign();
            varReplacer->replace(ps, xor_clause_inverted, group);
            return NULL;
        }
        default: {
            XorClause* c = clauseAllocator.XorClause_new(ps, xor_clause_inverted, group);
            attachClause(*c);
            return c;
        }
    }
}

template XorClause* Solver::addXorClauseInt(vec<Lit>& ps, bool xor_clause_inverted, const uint32_t group);
template XorClause* Solver::addXorClauseInt(XorClause& ps, bool xor_clause_inverted, const uint32_t group);

template<class T>
bool Solver::addXorClause(T& ps, bool xor_clause_inverted, const uint group, char* group_name)
{
    assert(decisionLevel() == 0);
    if (ps.size() > (0x01UL << 18)) {
        std::cout << "Too long clause!" << std::endl;
        exit(-1);
    }
    
    if (libraryCNFFile) {
        fprintf(libraryCNFFile, "x");
        for (uint32_t i = 0; i < ps.size(); i++) ps[i].print(libraryCNFFile);
        fprintf(libraryCNFFile, "0\n");
    }
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis) {
        logger.set_group_name(group, group_name);
        learnt_clause_group = std::max(group+1, learnt_clause_group);
    }
    #endif

    if (!ok)
        return false;
    assert(qhead == trail.size());

    // Check if clause is satisfied and remove false/duplicate literals:
    if (varReplacer->getNumLastReplacedVars() || subsumer->getNumElimed() || xorSubsumer->getNumElimed()) {
        for (uint32_t i = 0; i != ps.size(); i++) {
            if (subsumer->getVarElimed()[ps[i].var()] && !subsumer->unEliminate(ps[i].var()))
                return false;
            else if (xorSubsumer->getVarElimed()[ps[i].var()] && !xorSubsumer->unEliminate(ps[i].var()))
                return false;
            else {
                Lit otherLit = varReplacer->getReplaceTable()[ps[i].var()];
                if (otherLit.var() != ps[i].var()) {
                    ps[i] = Lit(otherLit.var(), false);
                    xor_clause_inverted ^= otherLit.sign();
                }
            }
        }
    }
    
    XorClause* c = addXorClauseInt(ps, xor_clause_inverted, group);
    if (c != NULL) xorclauses.push(c);

    return ok;
}

template bool Solver::addXorClause(vec<Lit>& ps, bool xor_clause_inverted, const uint group, char* group_name);
template bool Solver::addXorClause(XorClause& ps, bool xor_clause_inverted, const uint group, char* group_name);


template<class T>
bool Solver::addLearntClause(T& ps, const uint group, const uint32_t activity)
{
    Clause* c = addClauseInt(ps, group);
    if (c == NULL) return ok;

    //compensate for addClauseInt's attachClause, which doesn't know
    //that this is a learnt clause.
    clauses_literals -= c->size();
    learnts_literals += c->size();
    
    c->makeLearnt(activity);
    if (c->size() > 2) learnts.push(c);
    else {
        nbBin++;
        binaryClauses.push(c);
    }
    return ok;
}
template bool Solver::addLearntClause(Clause& ps, const uint group, const uint32_t activity);
template bool Solver::addLearntClause(vec<Lit>& ps, const uint group, const uint32_t activity);

template <class T>
Clause* Solver::addClauseInt(T& ps, uint group)
{
    assert(ok);
    
    std::sort(ps.getData(), ps.getDataEnd());
    Lit p = lit_Undef;
    uint32_t i, j;
    for (i = j = 0; i != ps.size(); i++) {
        if (value(ps[i]).getBool() || ps[i] == ~p)
            return NULL;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    }
    ps.shrink(i - j);
    
    if (ps.size() == 0) {
        ok = false;
        return NULL;
    } else if (ps.size() == 1) {
        uncheckedEnqueue(ps[0]);
        ok = (propagate().isNULL());
        return NULL;
    }

    Clause* c = clauseAllocator.Clause_new(ps, group);
    attachClause(*c);
    
    return c;
}

template Clause* Solver::addClauseInt(Clause& ps, const uint group);
template Clause* Solver::addClauseInt(vec<Lit>& ps, const uint group);

template<class T>
bool Solver::addClause(T& ps, const uint group, char* group_name)
{
    assert(decisionLevel() == 0);
    if (ps.size() > (0x01UL << 18)) {
        std::cout << "Too long clause!" << std::endl;
        exit(-1);
    }
    
    if (libraryCNFFile) {
        for (uint32_t i = 0; i != ps.size(); i++) ps[i].print(libraryCNFFile);
        fprintf(libraryCNFFile, "0\n");
    }
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis) {
        logger.set_group_name(group, group_name);
        learnt_clause_group = std::max(group+1, learnt_clause_group);
    }
    #endif

    if (!ok)
        return false;
    assert(qhead == trail.size());

    // Check if clause is satisfied and remove false/duplicate literals:
    if (varReplacer->getNumLastReplacedVars() || subsumer->getNumElimed() || xorSubsumer->getNumElimed()) {
        for (uint32_t i = 0; i != ps.size(); i++) {
            ps[i] = varReplacer->getReplaceTable()[ps[i].var()] ^ ps[i].sign();
            if (subsumer->getVarElimed()[ps[i].var()] && !subsumer->unEliminate(ps[i].var()))
                return false;
            if (xorSubsumer->getVarElimed()[ps[i].var()] && !xorSubsumer->unEliminate(ps[i].var()))
                return false;
        }
    }
    
    Clause* c = addClauseInt(ps, group);
    if (c != NULL) {
        if (c->size() > 2)
            clauses.push(c);
        else
            binaryClauses.push(c);
    }

    return ok;
}

template bool Solver::addClause(vec<Lit>& ps, const uint group, char* group_name);
template bool Solver::addClause(Clause& ps, const uint group, char* group_name);

void Solver::attachClause(XorClause& c)
{
    assert(c.size() > 2);
    #ifdef DEBUG_ATTACH
    assert(assigns[c[0].var()] == l_Undef);
    assert(assigns[c[1].var()] == l_Undef);
    #endif //DEBUG_ATTACH

    xorwatches[c[0].var()].push(clauseAllocator.getOffset((Clause*)&c));
    xorwatches[c[1].var()].push(clauseAllocator.getOffset((Clause*)&c));

    clauses_literals += c.size();
}

void Solver::attachClause(Clause& c)
{
    assert(c.size() > 1);
    uint32_t index0 = (~c[0]).toInt();
    uint32_t index1 = (~c[1]).toInt();
    
    if (c.size() == 2) {
        binwatches[index0].push(WatchedBin(c[1]));
        binwatches[index1].push(WatchedBin(c[0]));
    } else {
        ClauseOffset offset = clauseAllocator.getOffset(&c);
        watches[index0].push(Watched(offset, c[c.size()/2]));
        watches[index1].push(Watched(offset, c[c.size()/2]));
    }

    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size();
}


void Solver::detachClause(const XorClause& c)
{
    assert(c.size() > 1);
    ClauseOffset offset = clauseAllocator.getOffset(&c);
    assert(find(xorwatches[c[0].var()], offset));
    assert(find(xorwatches[c[1].var()], offset));
    remove(xorwatches[c[0].var()], offset);
    remove(xorwatches[c[1].var()], offset);

    clauses_literals -= c.size();
}

void Solver::detachClause(const Clause& c)
{
    assert(c.size() > 1);
    if (c.size() == 2) {
        assert(findWatchedBinCl(binwatches[(~c[0]).toInt()], c[1]));
        assert(findWatchedBinCl(binwatches[(~c[1]).toInt()], c[0]));
        
        removeWatchedBinCl(binwatches[(~c[0]).toInt()], c[1]);
        removeWatchedBinCl(binwatches[(~c[1]).toInt()], c[0]);
    } else {
        ClauseOffset offset = clauseAllocator.getOffset(&c);
        
        assert(findWatchedCl(watches[(~c[0]).toInt()], offset));
        assert(findWatchedCl(watches[(~c[1]).toInt()], offset));
        
        removeWatchedCl(watches[(~c[0]).toInt()], offset);
        removeWatchedCl(watches[(~c[1]).toInt()], offset);
    }
    
    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size();
}

void Solver::detachModifiedClause(const Lit lit1, const Lit lit2, const uint origSize, const Clause* address)
{
    assert(origSize > 1);
    
    if (origSize == 2) {
        assert(findWatchedBinCl(binwatches[(~lit1).toInt()], lit2));
        assert(findWatchedBinCl(binwatches[(~lit2).toInt()], lit1));
        removeWatchedBinCl(binwatches[(~lit1).toInt()], lit2);
        removeWatchedBinCl(binwatches[(~lit2).toInt()], lit1);
    } else {
        ClauseOffset offset = clauseAllocator.getOffset(address);
        assert(findW(watches[(~lit1).toInt()], offset));
        assert(findW(watches[(~lit2).toInt()], offset));
        removeW(watches[(~lit1).toInt()], offset);
        removeW(watches[(~lit2).toInt()], offset);
    }
    if (address->learnt()) learnts_literals -= origSize;
    else            clauses_literals -= origSize;
}

void Solver::detachModifiedClause(const Var var1, const Var var2, const uint origSize, const XorClause* address)
{
    assert(origSize > 2);

    ClauseOffset offset = clauseAllocator.getOffset(address);
    assert(find(xorwatches[var1], offset));
    assert(find(xorwatches[var2], offset));
    remove(xorwatches[var1], offset);
    remove(xorwatches[var2], offset);
    
    clauses_literals -= origSize;
}

// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level)
{
    #ifdef VERBOSE_DEBUG
    cout << "Canceling until level " << level;
    if (level > 0) cout << " sublevel: " << trail_lim[level];
    cout << endl;
    #endif
    
    if ((int)decisionLevel() > level) {
        
        #ifdef USE_GAUSS
        for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++)
            (*gauss)->canceling(trail_lim[level]);
        #endif //USE_GAUSS
        
        for (int sublevel = trail.size()-1; sublevel >= (int)trail_lim[level]; sublevel--) {
            Var var = trail[sublevel].var();
            #ifdef VERBOSE_DEBUG
            cout << "Canceling var " << var+1 << " sublevel: " << sublevel << endl;
            #endif
            #ifdef USE_OLD_POLARITIES
            polarity[var] = oldPolarity[var];
            #endif //USE_OLD_POLARITIES
            assigns[var] = l_Undef;
            insertVarOrder(var);
        }
        qhead = trail_lim[level];
        trail.shrink_(trail.size() - trail_lim[level]);
        trail_lim.shrink_(trail_lim.size() - level);
    }

    #ifdef VERBOSE_DEBUG
    cout << "Canceling finished. (now at level: " << decisionLevel() << " sublevel: " << trail.size()-1 << ")" << endl;
    #endif
}

void Solver::printLit(const Lit l) const
{
    printf("%s%d:%c", l.sign() ? "-" : "", l.var()+1, value(l) == l_True ? '1' : (value(l) == l_False ? '0' : 'X'));
}

void Solver::needLibraryCNFFile(const char* fileName)
{
    libraryCNFFile = fopen(fileName, "w");
    assert(libraryCNFFile != NULL);
}

#ifdef USE_GAUSS
void Solver::clearGaussMatrixes()
{
    for (uint i = 0; i < gauss_matrixes.size(); i++)
        delete gauss_matrixes[i];
    gauss_matrixes.clear();
}
#endif //USE_GAUSS

inline bool Solver::defaultPolarity()
{
    switch(polarity_mode) {
        case polarity_false:
            return true;
        case polarity_true:
            return false;
        case polarity_rnd:
            return mtrand.randInt(1);
        case polarity_auto:
            return true;
        default:
            assert(false);
    }
    
    return true;
}

void Solver::tallyVotes(const vec<Clause*>& cs, vector<double>& votes) const
{
    for (const Clause * const*it = cs.getData(), * const*end = it + cs.size(); it != end; it++) {
        const Clause& c = **it;
        if (c.learnt()) continue;
        
        double divider;
        if (c.size() > 63) divider = 0.0;
        else divider = 1.0/(double)((uint64_t)1<<(c.size()-1));
        
        for (const Lit *it2 = &c[0], *end2 = it2 + c.size(); it2 != end2; it2++) {
            if (it2->sign()) votes[it2->var()] += divider;
            else votes[it2->var()] -= divider;
        }
    }
}

void Solver::tallyVotes(const vec<XorClause*>& cs, vector<double>& votes) const
{
    for (const XorClause * const*it = cs.getData(), * const*end = it + cs.size(); it != end; it++) {
        const XorClause& c = **it;
        double divider;
        if (c.size() > 63) divider = 0.0;
        else divider = 1.0/(double)((uint64_t)1<<(c.size()-1));
        
        for (const Lit *it2 = &c[0], *end2 = it2 + c.size(); it2 != end2; it2++)
            votes[it2->var()] += divider;
    }
}

void Solver::calculateDefaultPolarities()
{
    #ifdef VERBOSE_DEBUG_POLARITIES
    std::cout << "Default polarities: " << std::endl;
    #endif
    
    assert(decisionLevel() == 0);
    if (polarity_mode == polarity_auto) {
        double time = cpuTime();
        
        vector<double> votes;
        votes.resize(nVars(), 0.0);
        
        tallyVotes(clauses, votes);
        tallyVotes(binaryClauses, votes);
        tallyVotes(varReplacer->getClauses(), votes);
        tallyVotes(xorclauses, votes);
        
        Var i = 0;
        uint32_t posPolars = 0;
        uint32_t undecidedPolars = 0;
        for (vector<double>::const_iterator it = votes.begin(), end = votes.end(); it != end; it++, i++) {
            polarity[i] = (*it >= 0.0);
            posPolars += (*it < 0.0);
            undecidedPolars += (*it == 0.0);
            #ifdef VERBOSE_DEBUG_POLARITIES
            std::cout << !defaultPolarities[i] << ", ";
            #endif //VERBOSE_DEBUG_POLARITIES
        }
        
        if (verbosity >= 2) {
            std::cout << "c |  Calc default polars - "
            << " time: " << std::fixed << std::setw(6) << std::setprecision(2) << cpuTime()-time << " s"
            << " pos: " << std::setw(7) << posPolars
            << " undec: " << std::setw(7) << undecidedPolars
            << " neg: " << std::setw(7) << nVars()-  undecidedPolars - posPolars
            << std::setw(8) << "    |" << std:: endl;
        }
    } else {
        std::fill(polarity.begin(), polarity.end(), defaultPolarity());
    }
    
    #ifdef VERBOSE_DEBUG_POLARITIES
    std::cout << std::endl;
    #endif //VERBOSE_DEBUG_POLARITIES
}

//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    #ifdef VERBOSE_DEBUG
    cout << "decision level: " << decisionLevel() << " ";
    #endif
    
    Var next = var_Undef;

    
    bool random = mtrand.randDblExc() < random_var_freq;
    
    // Random decision:
    if (random && !order_heap.empty()) {
        if (restrictedPickBranch == 0) next = order_heap[mtrand.randInt(order_heap.size()-1)];
        else next = order_heap[mtrand.randInt(std::min((uint32_t)order_heap.size()-1, restrictedPickBranch))];

        if (assigns[next] == l_Undef && decision_var[next])
            rnd_decisions++;
    }

    // Activity based decision:
    while (next == var_Undef || assigns[next] != l_Undef || !decision_var[next])
        if (order_heap.empty()) {
            next = var_Undef;
            break;
        } else {
            next = order_heap.removeMin();
        }

    bool sign;
    if (next != var_Undef) {
        if (simplifying && random)
            sign = mtrand.randInt(1);
        #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
        else if (avgBranchDepth.isvalid())
            sign = polarity[next] ^ (mtrand.randInt(avgBranchDepth.getavg() * ((lastSelectedRestartType == static_restart) ? 2 : 1) ) == 1);
        #endif
        else
            sign = polarity[next];
    }

    assert(next == var_Undef || value(next) == l_Undef);

    if (next == var_Undef) {
        #ifdef VERBOSE_DEBUG
        cout << "SAT!" << endl;
        #endif
        return lit_Undef;
    } else {
        Lit lit(next,sign);
        #ifdef VERBOSE_DEBUG
        assert(decision_var[lit.var()]);
        cout << "decided on: " << lit.var()+1 << " to set:" << !lit.sign() << endl;
        #endif
        return lit;
    }
}

// Assumes 'seen' is cleared (will leave it cleared)
template<class T1, class T2>
bool subset(const T1& A, const T2& B, vector<bool>& seen)
{
    for (uint i = 0; i != B.size(); i++)
        seen[B[i].toInt()] = 1;
    for (uint i = 0; i != A.size(); i++) {
        if (!seen[A[i].toInt()]) {
            for (uint i = 0; i != B.size(); i++)
                seen[B[i].toInt()] = 0;
            return false;
        }
    }
    for (uint i = 0; i != B.size(); i++)
        seen[B[i].toInt()] = 0;
    return true;
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|
|  Effect:
|    Will undo part of the trail, upto but not beyond the assumption of the current decision level.
|________________________________________________________________________________________________@*/
Clause* Solver::analyze(PropagatedFrom confl, vec<Lit>& out_learnt, int& out_btlevel, uint32_t &nbLevels, const bool update)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;
    out_btlevel = 0;

    PropagatedFrom oldConfl;

    do {
        assert(!confl.isNULL());          // (otherwise should be UIP)
        
        if (update && restartType == static_restart && !confl.isBinary() && confl.getClause()->learnt())
            claBumpActivity(*confl.getClause());

        for (uint j = (p == lit_Undef) ? 0 : 1, size = confl.size(); j != size; j++) {
            Lit q;
            if (j == 0 && confl.isBinary()) q = failBinLit;
            else q = confl[j];
            const Var my_var = q.var();

            if (!seen[my_var] && level[my_var] > 0) {
                varBumpActivity(my_var);
                seen[my_var] = 1;
                if (level[my_var] >= (int)decisionLevel()) {
                    pathC++;
                    #ifdef UPDATEVARACTIVITY
                    if (lastSelectedRestartType == dynamic_restart
                        && !reason[q.var()].isBinary()
                        && !reason[q.var()].isNULL()
                        && reason[q.var()].getClause()->learnt())
                        lastDecisionLevel.push(q.var());
                    #endif
                } else {
                    out_learnt.push(q);
                    if (level[my_var] > out_btlevel)
                        out_btlevel = level[my_var];
                }
            }
        }

        // Select next clause to look at:
        while (!seen[trail[index--].var()]);
        p     = trail[index+1];
        oldConfl = confl;
        confl = reason[p.var()];
        if (!confl.isBinary()) __builtin_prefetch(confl.getClause(), 1, 0);
        seen[p.var()] = 0;
        pathC--;

    } while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    uint32_t i, j;
    if (expensive_ccmin) {
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(out_learnt[i].var()); // (maintain an abstraction of levels involved in conflict)

        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason[out_learnt[i].var()].isNULL() || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
    } else {
        out_learnt.copyTo(analyze_toclear);
        for (i = j = 1; i < out_learnt.size(); i++) {
            PropagatedFrom c(reason[out_learnt[i].var()]);

            for (uint k = 1, size = c.size(); k < size; k++) {
                if (!seen[c[k].var()] && level[c[k].var()] > 0) {
                    out_learnt[j++] = out_learnt[i];
                    break;
                }
            }
        }
    }
    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else {
        uint32_t max_i = 1;
        for (uint32_t i = 2; i < out_learnt.size(); i++)
            if (level[out_learnt[i].var()] > level[out_learnt[max_i].var()])
                max_i = i;
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level[p.var()];
    }

    if (lastSelectedRestartType == dynamic_restart) {
        nbLevels = calcNBLevels(out_learnt);
        #ifdef UPDATEVARACTIVITY
        for(uint32_t i = 0; i != lastDecisionLevel.size(); i++) {
            PropagatedFrom cl = reason[lastDecisionLevel[i]];
            if (!cl.isBinary() && cl.getClause()->activity() < nbLevels)
                varBumpActivity(lastDecisionLevel[i]);
        }
        lastDecisionLevel.clear();
        #endif
    } else {
        nbLevels = 1000;
    }

    for (uint32_t j = 0; j != analyze_toclear.size(); j++)
        seen[analyze_toclear[j].var()] = 0;    // ('seen[]' is now cleared)
    
    if (out_learnt.size() == 1) return NULL;
    
    if (!oldConfl.isBinary() && !oldConfl.getClause()->isXor()
        && out_learnt.size() < oldConfl.getClause()->size()) {
        if (!subset(out_learnt, *oldConfl.getClause(), seen))
            return NULL;
        improvedClauseNo++;
        improvedClauseSize += oldConfl.getClause()->size() - out_learnt.size();
        return oldConfl.getClause();
    }
    
    return NULL;
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear();
    analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0) {
        assert(!reason[analyze_stack.last().var()].isNULL());
        PropagatedFrom c(reason[analyze_stack.last().var()]);
        
        analyze_stack.pop();

        for (uint i = 1, size = c.size(); i < size; i++) {
            Lit p  = c[i];
            if (!seen[p.var()] && level[p.var()] > 0) {
                if (!reason[p.var()].isNULL() && (abstractLevel(p.var()) & abstract_levels) != 0) {
                    seen[p.var()] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                } else {
                    for (uint32_t j = top; j != analyze_toclear.size(); j++)
                        seen[analyze_toclear[j].var()] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[p.var()] = 1;

    for (int32_t i = (int32_t)trail.size()-1; i >= (int32_t)trail_lim[0]; i--) {
        Var x = trail[i].var();
        if (seen[x]) {
            if (reason[x].isNULL()) {
                assert(level[x] > 0);
                out_conflict.push(~trail[i]);
            } else {
                PropagatedFrom c = reason[x];
                for (uint j = 1, size = c.size(); j < size; j++)
                    if (level[c[j].var()] > 0)
                        seen[c[j].var()] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[p.var()] = 0;
}


void Solver::uncheckedEnqueue(const Lit p, const PropagatedFrom& from)
{

    #ifdef DEBUG_UNCHECKEDENQUEUE_LEVEL0
    #ifndef VERBOSE_DEBUG
    if (decisionLevel() == 0)
    #endif //VERBOSE_DEBUG
    std::cout << "uncheckedEnqueue var " << p.var()+1 << " to " << !p.sign() << " level: " << decisionLevel() << " sublevel: " << trail.size() << std::endl;
    #endif //DEBUG_UNCHECKEDENQUEUE_LEVEL0

    //assert(decisionLevel() == 0 || !subsumer->getVarElimed()[p.var()]);
    
    assert(assigns[p.var()].isUndef());
    const Var v = p.var();
    assigns [v] = boolToLBool(!p.sign());//lbool(!sign(p));  // <<== abstract but not uttermost effecient
    level   [v] = decisionLevel();
    reason  [v] = from;
    #ifdef USE_OLD_POLARITIES
    oldPolarity[p.var()] = polarity[p.var()];
    #endif //USE_OLD_POLARITIES
    polarity[p.var()] = p.sign();
    trail.push(p);
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis)
        logger.propagation(p, from);
    #endif
}

/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise NULL.
|
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
PropagatedFrom Solver::propagate(const bool update)
{
    PropagatedFrom confl;
    uint32_t num_props = 0;
    
    #ifdef VERBOSE_DEBUG
    cout << "Propagation started" << endl;
    #endif
    uint32_t qheadBin = qhead;

    while (qhead < trail.size()) {
        
        //First propagate binary clauses
        while (qheadBin < trail.size()) {
            Lit p   = trail[qheadBin++];
            vec<WatchedBin> & wbin = binwatches[p.toInt()];
            num_props += wbin.size()/2;
            for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
                lbool val = value(k->impliedLit);
                if (val.isUndef()) {
                    uncheckedEnqueue(k->impliedLit, PropagatedFrom(p));
                } else if (val == l_False) {
                    confl = PropagatedFrom(p);
                    failBinLit = k->impliedLit;
                    //goto EndPropagate;
                }
            }
        }
        if (!confl.isNULL()) {
            goto EndPropagate;
        }

        //Next, propagate normal clauses
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watched>&  ws  = watches[p.toInt()];
        Watched        *i, *j, *end;
        num_props += ws.size();
        
        #ifdef VERBOSE_DEBUG
        cout << "Propagating lit " << (p.sign() ? '-' : ' ') << p.var()+1 << endl;
        #endif

        for (i = j = ws.getData(), end = ws.getDataEnd();  i != end;) {
            if (i+1 != end && !value((i+1)->blockedLit).getBool())
                __builtin_prefetch(clauseAllocator.getPointer((i+1)->clause), 1, 0);
            
            if(value(i->blockedLit).getBool()) { // Clause is sat
                *j++ = *i++;
                continue;
            }
            Lit bl = i->blockedLit;
            Clause& c = *clauseAllocator.getPointer(i->clause);
            ClauseOffset origClauseOffset = i->clause;
            i++;

            // Make sure the false literal is data[1]:
            const Lit false_lit(~p);
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;

            assert(c[1] == false_lit);

            // If 0th watch is true, then clause is already satisfied.
            const Lit& first = c[0];
            if (value(first).getBool()) {
                j->clause = origClauseOffset;
                j->blockedLit = first;
                j++;
            } else {
                // Look for new watch:
                for (Lit *k = &c[2], *end2 = c.getDataEnd(); k != end2; k++) {
                    if (value(*k) != l_False) {
                        c[1] = *k;
                        *k = false_lit;
                        watches[(~c[1]).toInt()].push(Watched(origClauseOffset, c[0]));
                        goto FoundWatch;
                    }
                }

                // Did not find watch -- clause is unit under assignment:
                j->clause = origClauseOffset;
                j->blockedLit = bl;
                j++;
                if (value(first) == l_False) {
                    confl = PropagatedFrom(&c);
                    qhead = trail.size();
                    // Copy the remaining watches:
                    while (i < end)
                        *j++ = *i++;
                } else {
                    uncheckedEnqueue(first, &c);
                    #ifdef DYNAMICNBLEVEL
                    if (update && c.learnt() && c.activity() > 2) { // GA
                        uint32_t nbLevels = calcNBLevels(c);
                        if (nbLevels+1 < c.activity())
                            c.setActivity(nbLevels);
                    }
                    #endif
                }
            }
FoundWatch:
            ;
        }
        ws.shrink_(i - j);

        //Finally, propagate XOR-clauses
        if (xorclauses.size() > 0 && confl.isNULL()) confl = propagate_xors(p);
    }
EndPropagate:
    propagations += num_props;
    simpDB_props -= num_props;
    
    #ifdef VERBOSE_DEBUG
    cout << "Propagation ended." << endl;
    #endif

    return confl;
}

PropagatedFrom Solver::propagateBin()
{
    while (qhead < trail.size()) {
        Lit p   = trail[qhead++];
        vec<WatchedBin> & wbin = binwatches[p.toInt()];
        propagations += wbin.size()/2;
        for(WatchedBin *k = wbin.getData(), *end = wbin.getDataEnd(); k != end; k++) {
            lbool val = value(k->impliedLit);
            if (val.isUndef()) {
                //uncheckedEnqueue(k->impliedLit, k->clause);
                uncheckedEnqueueLight(k->impliedLit);
            } else if (val == l_False) {
                return PropagatedFrom(p);
            }
        }
    }

    return PropagatedFrom();
}

template<class T>
inline const uint32_t Solver::calcNBLevels(const T& ps)
{
    MYFLAG++;
    uint32_t nbLevels = 0;
    for(const Lit *l = ps.getData(), *end = ps.getDataEnd(); l != end; l++) {
        int32_t lev = level[l->var()];
        if (permDiff[lev] != MYFLAG) {
            permDiff[lev] = MYFLAG;
            nbLevels++;
        }
    }
    return nbLevels;
}

PropagatedFrom Solver::propagate_xors(const Lit& p)
{
    #ifdef VERBOSE_DEBUG_XOR
    cout << "Xor-Propagating variable " <<  p.var()+1 << endl;
    #endif
    
    PropagatedFrom confl;

    vec<ClauseOffset>& ws = xorwatches[p.var()];
    ClauseOffset *i, *j, *end;
    for (i = j = ws.getData(), end = i + ws.size();  i != end;) {
        XorClause& c = *(XorClause*)clauseAllocator.getPointer(*i);
        ClauseOffset origClauseOffset = *i;
        i++;
        if (i != end)
            __builtin_prefetch(clauseAllocator.getPointer(*i), 1, 0);

        // Make sure the false literal is data[1]:
        if (c[0].var() == p.var()) {
            Lit tmp(c[0]);
            c[0] = c[1];
            c[1] = tmp;
        }
        assert(c[1].var() == p.var());
        
        #ifdef VERBOSE_DEBUG_XOR
        cout << "--> xor thing -- " << endl;
        printClause(c);
        cout << endl;
        #endif
        bool final = c.xor_clause_inverted();
        for (uint32_t k = 0, size = c.size(); k != size; k++ ) {
            const lbool& val = assigns[c[k].var()];
            if (val.isUndef() && k >= 2) {
                Lit tmp(c[1]);
                c[1] = c[k];
                c[k] = tmp;
                #ifdef VERBOSE_DEBUG_XOR
                cout << "new watch set" << endl << endl;
                #endif
                xorwatches[c[1].var()].push(origClauseOffset);
                goto FoundWatch;
            }

            c[k] = c[k].unsign() ^ val.getBool();
            final ^= val.getBool();
        }


        {
            // Did not find watch -- clause is unit under assignment:
            *j++ = origClauseOffset;

            #ifdef VERBOSE_DEBUG_XOR
            cout << "final: " << std::boolalpha << final << " - ";
            #endif
            if (assigns[c[0].var()].isUndef()) {
                c[0] = c[0].unsign()^final;
                
                #ifdef VERBOSE_DEBUG_XOR
                cout << "propagating ";
                printLit(c[0]);
                cout << endl;
                cout << "propagation clause -- ";
                printClause(*(Clause*)&c);
                cout << endl << endl;
                #endif
                
                uncheckedEnqueue(c[0], (Clause*)&c);
            } else if (!final) {
                
                #ifdef VERBOSE_DEBUG_XOR
                printf("conflict clause -- ");
                printClause(*(Clause*)&c);
                cout << endl << endl;
                #endif
                
                confl = PropagatedFrom((Clause*)&c);
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            } else {
                #ifdef VERBOSE_DEBUG_XOR
                printf("xor satisfied\n");
                #endif
                
                Lit tmp(c[0]);
                c[0] = c[1];
                c[1] = tmp;
            }
        }
FoundWatch:
        ;
    }
    ws.shrink_(i - j);

    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
bool  reduceDB_ltMiniSat::operator () (const Clause* x, const Clause* y) {
    const uint xsize = x->size();
    const uint ysize = y->size();
    
    // First criteria
    if (xsize > 2 && ysize == 2) return 1;
    if (ysize > 2 && xsize == 2) return 0;

    if (x->oldActivity() == y->oldActivity())
        return xsize > ysize;
    else return x->oldActivity() < y->oldActivity();
}
    
bool  reduceDB_ltGlucose::operator () (const Clause* x, const Clause* y) {
    const uint xsize = x->size();
    const uint ysize = y->size();
    
    // First criteria
    if (xsize > 2 && ysize == 2) return 1;
    if (ysize > 2 && xsize == 2) return 0;
    
    if (x->activity() > y->activity()) return 1;
    if (x->activity() < y->activity()) return 0;
    return xsize > ysize;
}

void Solver::reduceDB()
{
    uint32_t     i, j;

    nbReduceDB++;
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltMiniSat());
    
    #ifdef VERBOSE_DEBUG
    std::cout << "Cleaning clauses" << std::endl;
    for (uint i = 0; i != learnts.size(); i++) {
        std::cout << "activity:" << learnts[i]->activity()
        << " \toldActivity:" << learnts[i]->oldActivity()
        << " \tsize:" << learnts[i]->size() << std::endl;
    }
    #endif
    

    const uint removeNum = (double)learnts.size() / (double)RATIOREMOVECLAUSES;
    for (i = j = 0; i != removeNum; i++){
        //NOTE: The next instruciton only works if removeNum < learnts.size() (strictly smaller!!)
        __builtin_prefetch(learnts[i+1], 0, 0);
        if (learnts[i]->size() > 2 && !locked(*learnts[i]) && learnts[i]->activity() > 2) {
            removeClause(*learnts[i]);
        } else
            learnts[j++] = learnts[i];
    }
    for (; i < learnts.size(); i++) {
        learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);

    clauseAllocator.consolidate(this);
}

const vec<Clause*>& Solver::get_learnts() const
{
    return learnts;
}

const vec<Clause*>& Solver::get_sorted_learnts()
{
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltMiniSat());
    return learnts;
}

const vector<Lit> Solver::get_unitary_learnts() const
{
    vector<Lit> unitaries;
    if (decisionLevel() > 0) {
        for (uint32_t i = 0; i != trail_lim[0]; i++) {
            unitaries.push_back(trail[i]);
        }
    }
    
    return unitaries;
}

void Solver::dumpSortedLearnts(const char* file, const uint32_t maxSize)
{
    FILE* outfile = fopen(file, "w");
    if (!outfile) {
        printf("Error: Cannot open file '%s' to write learnt clauses!\n", file);
        exit(-1);
    }

    fprintf(outfile, "c \nc ---------\n");
    fprintf(outfile, "c unitaries\n");
    fprintf(outfile, "c ---------\n");
    for (uint32_t i = 0, end = (trail_lim.size() > 0) ? trail_lim[0] : trail.size() ; i < end; i++) {
        trail[i].printFull(outfile);
        #ifdef STATS_NEEDED
        if (dynamic_behaviour_analysis)
            fprintf(outfile, "c name of var: %s\n", logger.get_var_name(trail[i].var()).c_str());
        #endif //STATS_NEEDED
    }

    fprintf(outfile, "c conflicts %lu\n", (unsigned long)conflicts);
    if (maxSize == 1) goto end;

    fprintf(outfile, "c \nc ---------------------------------\n");
    fprintf(outfile, "c learnt clauses from binaryClauses\n");
    fprintf(outfile, "c ---------------------------------\n");
    for (uint i = 0; i != binaryClauses.size(); i++) {
        if (binaryClauses[i]->learnt()) {
            binaryClauses[i]->print(outfile);
        }
    }

    fprintf(outfile, "c \nc ---------------------------------------\n");
    fprintf(outfile, "c clauses representing 2-long XOR clauses\n");
    fprintf(outfile, "c ---------------------------------------\n");
    {
        const vector<Lit>& table = varReplacer->getReplaceTable();
        for (Var var = 0; var != table.size(); var++) {
            Lit lit = table[var];
            if (lit.var() == var)
                continue;

            fprintf(outfile, "%s%d %d 0\n", (!lit.sign() ? "-" : ""), lit.var()+1, var+1);
            fprintf(outfile, "%s%d -%d 0\n", (lit.sign() ? "-" : ""), lit.var()+1, var+1);
            #ifdef STATS_NEEDED
            if (dynamic_behaviour_analysis)
                fprintf(outfile, "c name of two vars that are anti/equivalent: '%s' and '%s'\n", logger.get_var_name(lit.var()).c_str(), logger.get_var_name(var).c_str());
            #endif //STATS_NEEDED
        }
    }
    fprintf(outfile, "c \nc --------------------n");
    fprintf(outfile, "c clauses from learnts\n");
    fprintf(outfile, "c --------------------n");
    if (lastSelectedRestartType == dynamic_restart)
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltGlucose());
    else
        std::sort(learnts.getData(), learnts.getData()+learnts.size(), reduceDB_ltMiniSat());
    for (int i = learnts.size()-1; i >= 0 ; i--) {
        if (learnts[i]->size() <= maxSize) {
            learnts[i]->print(outfile);
        }
    }

    end:
    
    fclose(outfile);
}

const uint32_t Solver::getNumElimSubsume() const
{
    return subsumer->getNumElimed();
}

const uint32_t Solver::getNumElimXorSubsume() const
{
    return xorSubsumer->getNumElimed();
}

const uint32_t Solver::getNumXorTrees() const
{
    return varReplacer->getNumTrees();
}

const uint32_t Solver::getNumXorTreesCrownSize() const
{
    return varReplacer->getNumReplacedVars();
}

const double Solver::getTotalTimeSubsumer() const
{
    return subsumer->getTotalTime();
}

const double Solver::getTotalTimeXorSubsumer() const
{
    return xorSubsumer->getTotalTime();
}


void Solver::setMaxRestarts(const uint num)
{
    maxRestarts = num;
}

inline int64_t abs64(int64_t a)
{
    if (a < 0) return -a;
    return a;
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
const bool Solver::simplify()
{
    testAllClauseAttach();
    assert(decisionLevel() == 0);

    if (!ok || !propagate().isNULL()) {
        ok = false;
        return false;
    }

    if (simpDB_props > 0) {
        return true;
    }
    
    double slowdown = (100000.0/(double)binaryClauses.size());
    slowdown = std::min(3.5, slowdown);
    slowdown = std::max(0.2, slowdown);
    
    double speedup = 50000000.0/(double)(propagations-lastSearchForBinaryXor);
    speedup = std::min(3.5, speedup);
    speedup = std::max(0.2, speedup);
    
    /*std::cout << "new:" << nbBin - lastNbBin + becameBinary << std::endl;
    std::cout << "left:" << ((double)(nbBin - lastNbBin + becameBinary)/BINARY_TO_XOR_APPROX) * slowdown  << std::endl;
    std::cout << "right:" << (double)order_heap.size() * PERCENTAGEPERFORMREPLACE * speedup << std::endl;*/
    
    if (findBinaryXors && regularlyFindBinaryXors &&
        (((double)abs64((int64_t)nbBin - (int64_t)lastNbBin + (int64_t)becameBinary)/BINARY_TO_XOR_APPROX) * slowdown) >
        ((double)order_heap.size() * PERCENTAGEPERFORMREPLACE * speedup)) {
        lastSearchForBinaryXor = propagations;

        clauseCleaner->cleanClauses(clauses, ClauseCleaner::clauses);
        clauseCleaner->cleanClauses(learnts, ClauseCleaner::learnts);
        clauseCleaner->removeSatisfied(binaryClauses, ClauseCleaner::binaryClauses);
        if (!ok) return false;
        testAllClauseAttach();

        XorFinder xorFinder(*this, binaryClauses, ClauseCleaner::binaryClauses);
        if (!xorFinder.doNoPart(2, 2)) return false;
        testAllClauseAttach();
        
        lastNbBin = nbBin;
        becameBinary = 0;
    }
    
    // Remove satisfied clauses:
    clauseCleaner->removeAndCleanAll();
    testAllClauseAttach();
    if (!ok) return false;
    
    if (performReplace && !varReplacer->performReplace())
        return false;

    // Remove fixed variables from the variable heap:
    order_heap.filter(VarFilter(*this));

    #ifdef USE_GAUSS
    for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end = gauss_matrixes.end(); gauss != end; gauss++) {
        if (!(*gauss)->full_init()) return false;
    }
    #endif //USE_GAUSS
    
    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    testAllClauseAttach();
    return true;
}


/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (nof_learnts : int) (params : const SearchParams&)  ->  [lbool]
|
|  Description:
|    Search for a model the specified number of conflicts, keeping the number of learnt clauses
|    below the provided limit. NOTE! Use negative value for 'nof_conflicts' or 'nof_learnts' to
|    indicate infinity.
|
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts, int nof_conflicts_fullrestart, const bool update)
{
    assert(ok);
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    llbool      ret;

    starts++;
    if (restartType == static_restart)
        staticStarts++;
    else
        dynStarts++;
    
    #ifdef USE_GAUSS
    for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end = gauss_matrixes.end(); gauss != end; gauss++) {
        if (!(*gauss)->full_init())
            return l_False;
    }
    #endif //USE_GAUSS

    testAllClauseAttach();
    findAllAttach();
    for (;;) {
        PropagatedFrom confl = propagate(update);

        if (!confl.isNULL()) {
            ret = handle_conflict(learnt_clause, confl, conflictC, update);
            if (ret != l_Nothing) return ret;
        } else {
            #ifdef USE_GAUSS
            bool at_least_one_continue = false;
            for (vector<Gaussian*>::iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++) {
                ret = (*gauss)->find_truths(learnt_clause, conflictC);
                if (ret == l_Continue) at_least_one_continue = true;
                else if (ret != l_Nothing) return ret;
            }
            if (at_least_one_continue) continue;
            #endif //USE_GAUSS
            ret = new_decision(nof_conflicts, nof_conflicts_fullrestart, conflictC);
            if (ret != l_Nothing) return ret;
        }
    }
}

llbool Solver::new_decision(const int& nof_conflicts, const int& nof_conflicts_fullrestart, int& conflictC)
{
    
    // Reached bound on number of conflicts?
    switch (restartType) {
    case dynamic_restart:
        if (nbDecisionLevelHistory.isvalid() &&
            ((nbDecisionLevelHistory.getavg()) > (totalSumOfDecisionLevel / (double)(conflicts - conflictsAtLastSolve)))) {
            
            #ifdef DEBUG_DYNAMIC_RESTART
            if (nbDecisionLevelHistory.isvalid()) {
                std::cout << "nbDecisionLevelHistory.getavg():" << nbDecisionLevelHistory.getavg() <<std::endl;
                //std::cout << "calculated limit:" << ((double)(nbDecisionLevelHistory.getavg())*0.9*((double)fullStarts + 20.0)/20.0) << std::endl;
                std::cout << "totalSumOfDecisionLevel:" << totalSumOfDecisionLevel << std::endl;
                std::cout << "conflicts:" << conflicts<< std::endl;
                std::cout << "conflictsAtLastSolve:" << conflictsAtLastSolve << std::endl;
                std::cout << "conflicts-conflictsAtLastSolve:" << conflicts-conflictsAtLastSolve<< std::endl;
                std::cout << "fullStarts:" << fullStarts << std::endl;
            }
            #endif
            
            nbDecisionLevelHistory.fastclear();
            #ifdef STATS_NEEDED
            if (dynamic_behaviour_analysis)
                progress_estimate = progressEstimate();
            #endif
            cancelUntil(0);
            return l_Undef;
        }
        break;
    case static_restart:
        if (nof_conflicts >= 0 && conflictC >= nof_conflicts) {
            #ifdef STATS_NEEDED
            if (dynamic_behaviour_analysis)
                progress_estimate = progressEstimate();
            #endif
            cancelUntil(0);
            return l_Undef;
        }
        break;
    case auto_restart:
        assert(false);
        break;
    }
    if (nof_conflicts_fullrestart >= 0 && (int)conflicts >= nof_conflicts_fullrestart)  {
        #ifdef STATS_NEEDED
        if (dynamic_behaviour_analysis)
            progress_estimate = progressEstimate();
        #endif
        cancelUntil(0);
        return l_Undef;
    }

    // Simplify the set of problem clauses:
    if (decisionLevel() == 0 && !simplify()) {
        return l_False;
    }

    // Reduce the set of learnt clauses:
    if (conflicts >= curRestart * nbclausesbeforereduce + nbCompensateSubsumer) {
        curRestart ++;
        reduceDB();
        nbclausesbeforereduce += 500;
    }

    Lit next = lit_Undef;
    while (decisionLevel() < assumptions.size()) {
        // Perform user provided assumption:
        Lit p = assumptions[decisionLevel()];
        if (value(p) == l_True) {
            // Dummy decision level:
            newDecisionLevel();
        } else if (value(p) == l_False) {
            analyzeFinal(~p, conflict);
            return l_False;
        } else {
            next = p;
            break;
        }
    }

    if (next == lit_Undef) {
        // New variable decision:
        decisions++;
        next = pickBranchLit();

        if (next == lit_Undef)
            return l_True;
    }

    // Increase decision level and enqueue 'next'
    assert(value(next) == l_Undef);
    newDecisionLevel();
    uncheckedEnqueue(next);

    return l_Nothing;
}

llbool Solver::handle_conflict(vec<Lit>& learnt_clause, PropagatedFrom confl, int& conflictC, const bool update)
{
    #ifdef VERBOSE_DEBUG
    cout << "Handling conflict: ";
    for (uint i = 0; i < learnt_clause.size(); i++)
        cout << learnt_clause[i].var()+1 << ",";
    cout << endl;
    #endif
    
    int backtrack_level;
    uint32_t nbLevels;

    conflicts++;
    conflictC++;
    if (decisionLevel() == 0)
        return l_False;
    learnt_clause.clear();
    Clause* c = analyze(confl, learnt_clause, backtrack_level, nbLevels, update);
    if (update) {
        #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
        avgBranchDepth.push(decisionLevel());
        #endif //RANDOM_LOOKAROUND_SEARCHSPACE
        if (restartType == dynamic_restart)
            nbDecisionLevelHistory.push(nbLevels);

        totalSumOfDecisionLevel += nbLevels;
    } else {
        conflictsAtLastSolve++;
    }
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis)
        logger.conflict(Logger::simple_confl_type, backtrack_level, confl->getGroup(), learnt_clause);
    #endif
    cancelUntil(backtrack_level);
    
    #ifdef VERBOSE_DEBUG
    cout << "Learning:";
    for (uint i = 0; i < learnt_clause.size(); i++) printLit(learnt_clause[i]), cout << " ";
    cout << endl;
    cout << "reverting var " << learnt_clause[0].var()+1 << " to " << !learnt_clause[0].sign() << endl;
    #endif
    
    assert(value(learnt_clause[0]) == l_Undef);
    //Unitary learnt
    if (learnt_clause.size() == 1) {
        uncheckedEnqueue(learnt_clause[0]);
        assert(backtrack_level == 0 && "Unit clause learnt, so must cancel until level 0, right?");
        
        #ifdef VERBOSE_DEBUG
        cout << "Unit clause learnt." << endl;
        #endif
    //Normal learnt
    } else {
        if (c) {
            detachClause(*c);
            for (uint32_t i = 0; i != learnt_clause.size(); i++)
                (*c)[i] = learnt_clause[i];
            c->resize(learnt_clause.size());
            if (c->learnt()) {
                if (c->activity() > nbLevels)
                    c->setActivity(nbLevels); // LS
                if (c->size() == 2)
                    nbBin++;
            }
            c->setStrenghtened();
        } else {
            c = clauseAllocator.Clause_new(learnt_clause, learnt_clause_group++, true);
            #ifdef STATS_NEEDED
            if (dynamic_behaviour_analysis)
                logger.set_group_name(c->getGroup(), "learnt clause");
            #endif
            if (c->size() > 2) {
                learnts.push(c);
                c->setActivity(nbLevels); // LS
            } else {
                binaryClauses.push(c);
                nbBin++;
            }
        }
        if (nbLevels <= 2) nbDL2++;
        attachClause(*c);
        uncheckedEnqueue(learnt_clause[0], c);
    }

    varDecayActivity();
    if (update && restartType == static_restart) claDecayActivity();

    return l_Nothing;
}

double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (uint32_t i = 0; i <= decisionLevel(); i++) {
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, (int)i) * (end - beg);
    }

    return progress / nVars();
}

#ifdef USE_GAUSS
void Solver::print_gauss_sum_stats()
{
    if (gauss_matrixes.size() == 0 && verbosity >= 2) {
        printf("  no matrixes found |\n");
        return;
    }
    
    uint called = 0;
    uint useful_prop = 0;
    uint useful_confl = 0;
    uint disabled = 0;
    for (vector<Gaussian*>::const_iterator gauss = gauss_matrixes.begin(), end= gauss_matrixes.end(); gauss != end; gauss++) {
        disabled += (*gauss)->get_disabled();
        called += (*gauss)->get_called();
        useful_prop += (*gauss)->get_useful_prop();
        useful_confl += (*gauss)->get_useful_confl();
        sum_gauss_unit_truths += (*gauss)->get_unit_truths();
        //gauss->print_stats();
        //gauss->print_matrix_stats();
    }
    sum_gauss_called += called;
    sum_gauss_confl += useful_confl;
    sum_gauss_prop += useful_prop;
    
    if (verbosity >= 2) {
        if (called == 0) {
            printf("      disabled      |\n");
        } else {
            printf(" %3.0lf%% |", (double)useful_prop/(double)called*100.0);
            printf(" %3.0lf%% |", (double)useful_confl/(double)called*100.0);
            printf(" %3.0lf%% |\n", 100.0-(double)disabled/(double)gauss_matrixes.size()*100.0);
        }
    }
}
#endif //USE_GAUSS

const bool Solver::chooseRestartType(const uint& lastFullRestart)
{
    uint relativeStart = starts - lastFullRestart;
    
    if (relativeStart > RESTART_TYPE_DECIDER_FROM  && relativeStart < RESTART_TYPE_DECIDER_UNTIL) {
        if (fixRestartType == auto_restart)
            restartTypeChooser->addInfo();
        
        if (relativeStart == (RESTART_TYPE_DECIDER_UNTIL-1)) {
            RestartType tmp;
            if (fixRestartType == auto_restart)
                tmp = restartTypeChooser->choose();
            else
                tmp = fixRestartType;
            
            if (tmp == dynamic_restart) {
                nbDecisionLevelHistory.fastclear();
                nbDecisionLevelHistory.initSize(100);
                if (verbosity >= 2)
                    printf("c |                           Decided on dynamic restart strategy                         |\n");
            } else  {
                if (verbosity >= 2)
                    printf("c |                            Decided on static restart strategy                         |\n");
                
                #ifdef USE_GAUSS
                if (!matrixFinder->findMatrixes()) return false;
                #endif //USE_GAUSS
            }
            lastSelectedRestartType = tmp;
            restartType = tmp;
            restartTypeChooser->reset();
        }
    }

    return true;
}

inline void Solver::setDefaultRestartType()
{
    if (fixRestartType != auto_restart) restartType = fixRestartType;
    else restartType = static_restart;
    
    if (restartType == dynamic_restart) {
        nbDecisionLevelHistory.fastclear();
        nbDecisionLevelHistory.initSize(100);
    }
    
    lastSelectedRestartType = restartType;
}

const lbool Solver::simplifyProblem(const uint32_t numConfls)
{
    testAllClauseAttach();
    #ifdef USE_GAUSS
    bool gauss_was_cleared = (gauss_matrixes.size() == 0);
    clearGaussMatrixes();
    #endif //USE_GAUSS

    StateSaver savedState(*this);;

    #ifdef BURST_SEARCH
    if (verbosity >= 2)
        std::cout << "c | " << std::setw(24) << " " 
        << "Simplifying problem for " << std::setw(8) << numConfls << " confls" 
        << std::setw(24) << " |" << std::endl;
    random_var_freq = 1;
    simplifying = true;
    uint64_t origConflicts = conflicts;
    #endif //BURST_SEARCH
    
    lbool status = l_Undef;

    #ifdef BURST_SEARCH
    restartType = static_restart;
    
    while(status == l_Undef && conflicts-origConflicts < numConfls) {
        printRestartStat();
        status = search(100, -1, false);
        starts--;
    }
    if (status != l_Undef)
        goto end;
    printRestartStat();
    #endif //BURST_SEARCH

    if (doXorSubsumption && !xorSubsumer->simplifyBySubsumption()) {
        status = l_False;
        goto end;
    }
    testAllClauseAttach();

    if (failedVarSearch && !failedVarSearcher->search((nClauses() < 500000 && order_heap.size() < 50000) ? 9000000 : 3000000))  {
        status = l_False;
        goto end;
    }
    testAllClauseAttach();

    if (performReplace && (regularRemoveUselessBins || regularSubsumeWithNonExistBinaries)) {
        OnlyNonLearntBins onlyNonLearntBins(*this);
        if (!onlyNonLearntBins.fill()) {
            status = l_False;
            goto end;
        }
        if (regularRemoveUselessBins) {
            UselessBinRemover uselessBinRemover(*this, onlyNonLearntBins);
            if (!uselessBinRemover.removeUslessBinFull()) {
                status = l_False;
                goto end;
            }
        }
        if (regularSubsumeWithNonExistBinaries
            && !subsumer->subsumeWithBinaries(&onlyNonLearntBins)) {
            status = l_False;
            goto end;
        }
    }

    if (doSubsumption && !subsumer->simplifyBySubsumption(false)) {
        status = l_False;
        goto end;
    }
    if (doSubsumption && !subsumer->simplifyBySubsumption(true)) {
        status = l_False;
        goto end;
    }
    testAllClauseAttach();
    
    /*if (findNormalXors && xorclauses.size() > 200 && clauses.size() < MAX_CLAUSENUM_XORFIND/8) {
        XorFinder xorFinder(*this, clauses, ClauseCleaner::clauses);
        if (!xorFinder.doNoPart(3, 7)) {
            status = l_False;
            goto end;
        }
    } else*/ if (xorclauses.size() <= 200 && xorclauses.size() > 0 && nClauses() > 10000) {
        XorFinder x(*this, clauses, ClauseCleaner::clauses);
        x.addAllXorAsNorm();
    }
    
end:
    #ifdef BURST_SEARCH
    if (verbosity >= 2)
        printf("c                                      Simplifying finished                               |\n");
    #endif //#ifdef BURST_SEARCH


    savedState.restore();
    simplifying = false;
    
    #ifdef USE_GAUSS
    if (status == l_Undef && !gauss_was_cleared && !matrixFinder->findMatrixes())
        status = l_False;
    #endif //USE_GAUSS

    testAllClauseAttach();
    return status;
}

const bool Solver::checkFullRestart(int& nof_conflicts, int& nof_conflicts_fullrestart, uint& lastFullRestart)
{
    if (nof_conflicts_fullrestart > 0 && (int)conflicts >= nof_conflicts_fullrestart) {
        #ifdef USE_GAUSS
        clearGaussMatrixes();
        #endif //USE_GAUSS
        if (verbosity >= 2)
            printf("c |                                      Fully restarting                                 |\n");
        nof_conflicts = restart_first + (double)restart_first*restart_inc;
        nof_conflicts_fullrestart = (double)nof_conflicts_fullrestart * FULLRESTART_MULTIPLIER_MULTIPLIER;
        restartType = static_restart;
        lastFullRestart = starts;
        
        /*if (findNormalXors && clauses.size() < MAX_CLAUSENUM_XORFIND) {
            XorFinder xorFinder(this, clauses, ClauseCleaner::clauses);
            if (!xorFinder.doNoPart(3, 10))
                return false;
        }*/
        
        if (doPartHandler && !partHandler->handle())
            return false;
        
        //calculateDefaultPolarities();
        
        fullStarts++;
    }
    
    return true;
}

inline void Solver::performStepsBeforeSolve()
{
    assert(qhead == trail.size());
    testAllClauseAttach();

    if (performReplace && !varReplacer->performReplace()) return;

    if (doSubsumption && !subsumer->simplifyBySubsumption(true)) {
        return;
    }

    if (performReplace) {
        OnlyNonLearntBins onlyNonLearntBins(*this);
        if (!onlyNonLearntBins.fill()) return;
        if (regularRemoveUselessBins) {
            UselessBinRemover uselessBinRemover(*this, onlyNonLearntBins);
            if (!uselessBinRemover.removeUslessBinFull()) return;
        }
        if (subsumeWithNonExistBinaries
            && !subsumer->subsumeWithBinaries(&onlyNonLearntBins)) return;
    }

    if (doSubsumption
        && !libraryUsage
        && clauses.size() + binaryClauses.size() + learnts.size() < 4800000
        && !subsumer->simplifyBySubsumption())
        return;

    /*
    if (conflicts == 0 && learnts.size() == 0
        && noLearntBinaries()) {
        if (subsumeWithNonExistBinaries && !subsumer->subsumeWithBinaries(true)) return;
        OnlyNonLearntBins onlyNonLearntBins(*this);
        if (!onlyNonLearntBins.fill()) return;
        if (regularRemoveUselessBins) {
            UselessBinRemover uselessBinRemover(*this, onlyNonLearntBins);
            if (!uselessBinRemover.removeUslessBinFull()) return;
        }
    }
    */

    if (findBinaryXors && binaryClauses.size() < MAX_CLAUSENUM_XORFIND) {
        XorFinder xorFinder(*this, binaryClauses, ClauseCleaner::binaryClauses);
        if (!xorFinder.doNoPart(2, 2)) return;
        if (performReplace && !varReplacer->performReplace(true)) return;
    }

    if (findNormalXors && clauses.size() < MAX_CLAUSENUM_XORFIND) {
        XorFinder xorFinder(*this, clauses, ClauseCleaner::clauses);
        if (!xorFinder.doNoPart(3, 7)) return;
    }
    
    if (xorclauses.size() > 1) {
        testAllClauseAttach();
        if (doXorSubsumption && !xorSubsumer->simplifyBySubsumption())
            return;
        
        testAllClauseAttach();
        if (performReplace && !varReplacer->performReplace())
            return;
    }
}

void Solver::checkSolution()
{
    // Extend & check:
    model.growTo(nVars());
    for (Var var = 0; var != nVars(); var++) model[var] = value(var);
    verifyModel();
    model.clear();
}

lbool Solver::solve(const vec<Lit>& assumps)
{
#ifdef VERBOSE_DEBUG
    std::cout << "Solver::solve() called" << std::endl;
#endif
    if (!ok) return l_False;
    assert(qhead == trail.size());
    
    if (libraryCNFFile)
        fprintf(libraryCNFFile, "c Solver::solve() called\n");
    
    model.clear();
    conflict.clear();
    #ifdef USE_GAUSS
    clearGaussMatrixes();
    #endif //USE_GAUSS
    setDefaultRestartType();
    totalSumOfDecisionLevel = 0;
    conflictsAtLastSolve = conflicts;
    #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
    avgBranchDepth.fastclear();
    avgBranchDepth.initSize(500);
    #endif //RANDOM_LOOKAROUND_SEARCHSPACE
    starts = 0;

    assumps.copyTo(assumptions);

    int  nof_conflicts = restart_first;
    int  nof_conflicts_fullrestart = restart_first * FULLRESTART_MULTIPLIER + conflicts;
    //nof_conflicts_fullrestart = -1;
    uint    lastFullRestart  = starts;
    lbool   status        = l_Undef;
    uint64_t nextSimplify = restart_first * SIMPLIFY_MULTIPLIER + conflicts;
    
    if (nClauses() * learntsize_factor < nbclausesbeforereduce) {
        if (nClauses() * learntsize_factor < nbclausesbeforereduce/2)
            nbclausesbeforereduce = nbclausesbeforereduce/4;
        else
            nbclausesbeforereduce = (nClauses() * learntsize_factor)/2;
    }
    testAllClauseAttach();
    findAllAttach();
    
    if (conflicts == 0) {
        performStepsBeforeSolve();
        if (!ok) return l_False;
    
        printStatHeader();
    }
    calculateDefaultPolarities();
    
    // Search:
    while (status == l_Undef && starts < maxRestarts) {
        #ifdef DEBUG_VARELIM
        assert(subsumer->checkElimedUnassigned());
        assert(xorSubsumer->checkElimedUnassigned());
        #endif //DEBUG_VARELIM
        
        if (schedSimplification && conflicts >= nextSimplify) {
            status = simplifyProblem(500);
            nextSimplify = conflicts * 1.5;
            if (status != l_Undef) break;
        }
        
        printRestartStat();
        #ifdef STATS_NEEDED
        if (dynamic_behaviour_analysis) {
            logger.end(Logger::restarting);
            logger.begin();
        }
        #endif
        
        status = search(nof_conflicts, nof_conflicts_fullrestart);
        nof_conflicts = (double)nof_conflicts * restart_inc;
        if (status != l_Undef) break;
        if (!checkFullRestart(nof_conflicts, nof_conflicts_fullrestart, lastFullRestart))
            return l_False;
        if (!chooseRestartType(lastFullRestart))
            return l_False;
        #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
        //if (avgBranchDepth.isvalid())
        //    std::cout << "avg branch depth:" << avgBranchDepth.getavg() << std::endl;
        #endif //RANDOM_LOOKAROUND_SEARCHSPACE
    }
    printEndSearchStat();
    
    #ifdef USE_GAUSS
    for (uint i = 0; i < gauss_matrixes.size(); i++)
        delete gauss_matrixes[i];
    gauss_matrixes.clear();
    #endif //USE_GAUSS

#ifdef VERBOSE_DEBUG
    if (status == l_True)
        std::cout << "Solution  is SAT" << std::endl;
    else if (status == l_False)
        std::cout << "Solution is UNSAT" << std::endl;
    else
        std::cout << "Solutions is UNKNOWN" << std::endl;
#endif //VERBOSE_DEBUG

    if (status == l_True) {
        if (greedyUnbound) {
            double time = cpuTime();
            FindUndef finder(*this);
            const uint unbounded = finder.unRoll();
            if (verbosity >= 1)
                printf("c Greedy unbounding     :%5.2lf s, unbounded: %7d vars\n", cpuTime()-time, unbounded);
        }

        partHandler->addSavedState();
        varReplacer->extendModelPossible();
#ifndef NDEBUG
        //checkSolution();
#endif
        
        if (subsumer->getNumElimed() || xorSubsumer->getNumElimed()) {
            if (verbosity >= 1) {
                std::cout << "c Solution needs extension. Extending." << std::endl;
            }
            Solver s;
            s.doSubsumption = false;
            s.performReplace = false;
            s.findBinaryXors = false;
            s.findNormalXors = false;
            s.failedVarSearch = false;
            s.conglomerateXors = false;
            s.subsumeWithNonExistBinaries = false;
            s.regularSubsumeWithNonExistBinaries = false;
            s.removeUselessBins = false;
            s.regularRemoveUselessBins = false;
            s.greedyUnbound = greedyUnbound;
            for (Var var = 0; var < nVars(); var++) {
                s.newVar(decision_var[var] || subsumer->getVarElimed()[var] || varReplacer->varHasBeenReplaced(var) || xorSubsumer->getVarElimed()[var]);
                
                //assert(!(xorSubsumer->getVarElimed()[var] && (decision_var[var] || subsumer->getVarElimed()[var] || varReplacer->varHasBeenReplaced(var))));
                
                if (value(var) != l_Undef) {
                    vec<Lit> tmp;
                    tmp.push(Lit(var, value(var) == l_False));
                    s.addClause(tmp);
                }
            }
            varReplacer->extendModelImpossible(s);
            subsumer->extendModel(s);
            xorSubsumer->extendModel(s);
            
            status = s.solve();
            if (status != l_True) {
                printf("c ERROR! Extension of model failed!\n");
                assert(status == l_True);
                exit(-1);
            }
#ifdef VERBOSE_DEBUG
            std::cout << "Solution extending finished." << std::endl;
#endif
            for (Var var = 0; var < nVars(); var++) {
                if (assigns[var] == l_Undef && s.model[var] != l_Undef) uncheckedEnqueue(Lit(var, s.model[var] == l_False));
            }
            ok = (propagate().isNULL());
            if (!ok) {
                printf("c ERROR! Extension of model failed!\n");
                assert(ok);
                exit(-1);
            }
        }
#ifndef NDEBUG
        //checkSolution();
#endif
        //Copy model:
        model.growTo(nVars());
        for (Var var = 0; var != nVars(); var++) model[var] = value(var);
    }
    
    if (status == l_False) {
        if (conflict.size() == 0)
            ok = false;
    }
    
    #ifdef STATS_NEEDED
    if (dynamic_behaviour_analysis) {
        if (status == l_True)
            logger.end(Logger::model_found);
        else if (status == l_False)
                logger.end(Logger::unsat_model_found);
        else if (status == l_Undef)
            logger.end(Logger::restarting);
    }
    #endif
    
    #ifdef LS_STATS_NBBUMP
    for(int i=0;i<learnts.size();i++)
        printf("## %d %d %d\n", learnts[i]->size(),learnts[i]->activity(),
               (uint)learnts[i]->nbBump());
    #endif

    cancelUntil(0);
    if (doPartHandler && status != l_False) partHandler->readdRemovedClauses();
    restartTypeChooser->reset();
    
#ifdef VERBOSE_DEBUG
    std::cout << "Solver::solve() finished" << std::endl;
#endif
    return status;
}

//=================================================================================================
// Debug methods:

bool Solver::verifyXorClauses(const vec<XorClause*>& cs) const
{
    #ifdef VERBOSE_DEBUG
    cout << "Checking xor-clauses whether they have been properly satisfied." << endl;;
    #endif
    
    bool failed = false;
    
    for (uint32_t i = 0; i != xorclauses.size(); i++) {
        XorClause& c = *xorclauses[i];
        bool final = c.xor_clause_inverted();
        
        #ifdef VERBOSE_DEBUG
        XorClause* c2 = XorClause_new(c, c.xor_clause_inverted(), c.getGroup());
        std::sort(c2->getData(), c2->getData()+ c2->size());
        c2->plainPrint();
        clauseFree(c2);
        #endif
        
        for (uint j = 0; j < c.size(); j++) {
            assert(modelValue(c[j].unsign()) != l_Undef);
            final ^= (modelValue(c[j].unsign()) == l_True);
        }
        if (!final) {
            printf("unsatisfied clause: ");
            xorclauses[i]->plainPrint();
            failed = true;
        }
    }
    
    return failed;
}

bool Solver::verifyClauses(const vec<Clause*>& cs) const
{
    #ifdef VERBOSE_DEBUG
    cout << "Checking clauses whether they have been properly satisfied." << endl;;
    #endif
    
    bool failed = false;
    
    for (uint32_t i = 0; i != cs.size(); i++) {
        Clause& c = *cs[i];
        for (uint j = 0; j < c.size(); j++)
            if (modelValue(c[j]) == l_True)
                goto next;
            
        printf("unsatisfied clause: ");
        cs[i]->plainPrint();
        failed = true;
    next:
        ;
    }
    
    return failed;
}

void Solver::verifyModel()
{
    assert(!verifyClauses(clauses));
    assert(!verifyClauses(binaryClauses));
    assert(!verifyXorClauses(xorclauses));

    if (verbosity >=1)
        printf("c Verified %d clauses.\n", clauses.size() + xorclauses.size());
}


void Solver::checkLiteralCount()
{
    // Check that sizes are calculated correctly:
    int cnt = 0;
    for (uint32_t i = 0; i != clauses.size(); i++)
        cnt += clauses[i]->size();

    for (uint32_t i = 0; i != xorclauses.size(); i++)
        cnt += xorclauses[i]->size();

    if ((int)clauses_literals != cnt) {
        fprintf(stderr, "literal count: %d, real value = %d\n", (int)clauses_literals, cnt);
        assert((int)clauses_literals == cnt);
    }
}

void Solver::printStatHeader() const
{
    #ifdef STATS_NEEDED
    if (verbosity >= 1 && !(dynamic_behaviour_analysis && logger.statistics_on)) {
    #else
    if (verbosity >= 1) {
    #endif
        printf("c ============================[ Search Statistics ]========================================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          |        GAUSS       |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl | Prop   Confl   On  |\n");
        printf("c =========================================================================================\n");
    }
}

void Solver::printRestartStat()
{
    if (verbosity >= 2) {
        printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f |", (int)conflicts, (int)order_heap.size(), (int)(nClauses()-nbBin), (int)clauses_literals, (int)(nbclausesbeforereduce*curRestart+nbCompensateSubsumer), (int)(nLearnts()+nbBin), (double)learnts_literals/(double)(nLearnts()+nbBin));
    }
    
    #ifdef USE_GAUSS
    print_gauss_sum_stats();
    #else //USE_GAUSS
    if (verbosity >= 2) {
        printf("                    |\n");
    }
    #endif //USE_GAUSS
}

void Solver::printEndSearchStat()
{
    #ifdef STATS_NEEDED
    if (verbosity >= 1 && !(dynamic_behaviour_analysis && logger.statistics_on)) {
    #else
    if (verbosity >= 1) {
    #endif //STATS_NEEDED
        printf("c ====================================================================");
        #ifdef USE_GAUSS
        print_gauss_sum_stats();
        if (verbosity == 1) printf("=====================\n");
        #else //USE_GAUSS
        printf("\n");
        #endif //USE_GAUSS
    }
}

#ifdef DEBUG_ATTACH
void Solver::testAllClauseAttach() const
{
    for (Clause *const*it = clauses.getData(), *const*end = clauses.getDataEnd(); it != end; it++) {
        const Clause& c = **it;
        if (c.size() > 2) {
            assert(findWatchedCl(watches[(~c[0]).toInt()], &c));
            assert(findWatchedCl(watches[(~c[1]).toInt()], &c));
        } else {
            assert(findWatchedBinCl(binwatches[(~c[0]).toInt()], &c));
            assert(findWatchedBinCl(binwatches[(~c[1]).toInt()], &c));
        }
    }
    
    for (Clause *const*it = binaryClauses.getData(), *const*end = binaryClauses.getDataEnd(); it != end; it++) {
        const Clause& c = **it;
        assert(c.size() == 2);
        assert(findWatchedBinCl(binwatches[(~c[0]).toInt()], &c));
        assert(findWatchedBinCl(binwatches[(~c[1]).toInt()], &c));
    }
    
    for (XorClause *const*it = xorclauses.getData(), *const*end = xorclauses.getDataEnd(); it != end; it++) {
        const XorClause& c = **it;
        assert(find(xorwatches[c[0].var()], &c));
        assert(find(xorwatches[c[1].var()], &c));
        if (assigns[c[0].var()]!=l_Undef || assigns[c[1].var()]!=l_Undef) {
            for (uint i = 0; i < c.size();i++) {
                assert(assigns[c[i].var()] != l_Undef);
            }
        }
    }
}

void Solver::findAllAttach() const
{
    for (uint32_t i = 0; i < binwatches.size(); i++) {
        for (uint32_t i2 = 0; i2 < binwatches[i].size(); i2++) {
            assert(findClause(binwatches[i][i2].clause));
        }
    }
    for (uint32_t i = 0; i < watches.size(); i++) {
        for (uint32_t i2 = 0; i2 < watches[i].size(); i2++) {
            assert(findClause(watches[i][i2].clause));
        }
    }

    for (uint32_t i = 0; i < xorwatches.size(); i++) {
        for (uint32_t i2 = 0; i2 < xorwatches[i].size(); i2++) {
            assert(findClause(xorwatches[i][i2]));
        }
    }
}

const bool Solver::findClause(XorClause* c) const
{
    for (uint32_t i = 0; i < xorclauses.size(); i++) {
        if (xorclauses[i] == c) return true;
    }
    return false;
}

const bool Solver::findClause(Clause* c) const
{
    for (uint32_t i = 0; i < binaryClauses.size(); i++) {
        if (binaryClauses[i] == c) return true;
    }
    for (uint32_t i = 0; i < clauses.size(); i++) {
        if (clauses[i] == c) return true;
    }
    for (uint32_t i = 0; i < learnts.size(); i++) {
        if (learnts[i] == c) return true;
    }
    vec<Clause*> cs = varReplacer->getClauses();
    for (uint32_t i = 0; i < cs.size(); i++) {
        if (cs[i] == c) return true;
    }
    
    return false;
}
#endif //DEBUG_ATTACH

const bool Solver::noLearntBinaries() const
{
    for (uint32_t i = 0; i < binaryClauses.size(); i++) {
        if (binaryClauses[i]->learnt()) return false;
    }

    return true;
}

}; //NAMESPACE MINISAT
