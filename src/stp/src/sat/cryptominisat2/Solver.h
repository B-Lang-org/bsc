/****************************************************************************************[Solver.h]
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

#ifndef SOLVER_H
#define SOLVER_H

#include <cstdio>
#include <string.h>
#include <stdio.h>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "time_mem.h"
#include "Vec.h"
#include "Heap.h"
#include "Alg.h"
#include "MersenneTwister.h"
#include "SolverTypes.h"
#include "Clause.h"
#include "Logger.h"
#include "constants.h"
#include "BoundedQueue.h"
#include "GaussianConfig.h"

namespace MINISAT
{
using namespace MINISAT;

class Gaussian;
class MatrixFinder;
class Conglomerate;
class VarReplacer;
class XorFinder;
class FindUndef;
class ClauseCleaner;
class FailedVarSearcher;
class Subsumer;
class XorSubsumer;
class PartHandler;
class RestartTypeChooser;
class StateSaver;
class UselessBinRemover;

#ifdef VERBOSE_DEBUG
#define DEBUG_UNCHECKEDENQUEUE_LEVEL0
using std::cout;
using std::endl;
#endif

//=================================================================================================
// Solver -- the main class:

struct reduceDB_ltMiniSat
{
    bool operator () (const Clause* x, const Clause* y);
};

struct reduceDB_ltGlucose
{
    bool operator () (const Clause* x, const Clause* y);
};

//#define DEBUG_PROPAGATEFROM

class PropagatedFrom
{
    private:
        union {Clause* clause; uint32_t otherLit;};
        
    public:
        PropagatedFrom(Clause* c)
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(c != NULL);
            #endif
            clause = c;
        }

        PropagatedFrom(const Lit& _other)
        {
            otherLit = _other.toInt() << 1;
            otherLit |= 1;
        }

        PropagatedFrom() :
            clause(NULL)
        {
        }

        const bool isBinary() const
        {
            return (otherLit&1);
        }

        const Lit getOtherLit() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(isBinary());
            #endif
            return Lit::toLit(otherLit>>1);
        }

        const Clause* getClause() const
        {
            #ifdef DEBUG_PROPAGATEFROM
            assert(!isBinary());
            #endif
            return clause;
        }

        Clause* getClause()
        {
            return clause;
        }

        const bool isNULL() const
        {
            if (isBinary()) return false;
            return clause == NULL;
        }

        const uint32_t size() const
        {
            if (isBinary()) return 2;
            
            #ifdef DEBUG_PROPAGATEFROM
            assert(!isNULL());
            #endif
            
            return getClause()->size();
        }

        const Lit operator[](uint32_t i) const
        {
            if (isBinary()) {
                #ifdef DEBUG_PROPAGATEFROM
                assert(i == 1);
                #endif
                return getOtherLit();
            }

            #ifdef DEBUG_PROPAGATEFROM
            assert(!isNULL());
            #endif
            return (*getClause())[i];
        }
};

class Solver
{
public:

    // Constructor/Destructor:
    //
    Solver();
    ~Solver();

    // Problem specification:
    //
    Var     newVar    (bool dvar = true); // Add a new variable with parameters specifying variable mode.
    template<class T>
    bool    addClause (T& ps, const uint group = 0, char* group_name = NULL);  // Add a clause to the solver. NOTE! 'ps' may be shrunk by this method!
    template<class T>
    bool    addXorClause (T& ps, bool xor_clause_inverted, const uint group = 0, char* group_name = NULL);  // Add a xor-clause to the solver. NOTE! 'ps' may be shrunk by this method!

    // Solving:
    //
    lbool    solve       (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool    solve       ();                        // Search without assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    // Variable mode:
    //
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.
    void    setSeed (const uint32_t seed);  // Sets the seed to be the given number
    void    setMaxRestarts(const uint num); //sets the maximum number of restarts to given value

    // Read state:
    //
    lbool   value      (const Var& x) const;       // The current value of a variable.
    lbool   value      (const Lit& p) const;       // The current value of a literal.
    lbool   modelValue (const Lit& p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    uint32_t     nAssigns   ()      const;       // The current number of assigned literals.
    uint32_t     nClauses   ()      const;       // The current number of original clauses.
    uint32_t     nLiterals  ()      const;       // The current number of total literals.
    uint32_t     nLearnts   ()      const;       // The current number of learnt clauses.
    uint32_t     nVars      ()      const;       // The current number of variables.

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
    // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    double    random_var_freq;    // The frequency with which the decision heuristic tries to choose a random variable.        (default 0.02)
    double    clause_decay;       // Inverse of the clause activity decay factor.                                              (1 / 0.999)
    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)
    bool      expensive_ccmin;    // Controls conflict clause minimization.                                                    (default TRUE)
    int       polarity_mode;      // Controls which polarity the decision heuristic chooses. See enum below for allowed modes. (default polarity_false)
    int       verbosity;          // Verbosity level. 0=silent, 1=some progress report                                         (default 0)
    Var       restrictedPickBranch; // Pick variables to branch on preferentally from the highest [0, restrictedPickBranch]. If set to 0, preferentiality is turned off (i.e. picked randomly between [0, all])
    bool      findNormalXors;     // Automatically find non-binary xor-clauses and convert them
    bool      findBinaryXors;     // Automatically find binary xor-clauses and convert them
    bool      regularlyFindBinaryXors; // Regularly find binary xor-clauses and convert them
    bool      performReplace;       // Should var-replacing be performed?
    bool      conglomerateXors;   // Conglomerate XORs
    bool      heuleProcess;       // Process XORs according to Heule
    bool      schedSimplification;// Schedule simplification
    bool      doSubsumption;        // Should try to subsume clauses
    bool      doXorSubsumption;     // Should try to subsume xor clauses
    bool      doPartHandler;        // Should try to subsume clauses
    bool      doHyperBinRes;        // Should try carry out hyper-binary resolution
    bool      doBlockedClause;      // Should try to remove blocked clauses
    bool      doVarElim;            // Perform variable elimination
    bool      doSubsume1;           // Perform clause contraction through resolution
    bool      failedVarSearch;      // Should search for failed vars and doulbly propagated vars
    bool      addExtraBins;         // Should add extra binaries in failed literal probing
    bool      removeUselessBins;    // Should try to remove useless binary clauses
    bool      regularRemoveUselessBins; // Should try to remove useless binary clauses regularly
    bool      subsumeWithNonExistBinaries;
    bool      regularSubsumeWithNonExistBinaries;
    bool      libraryUsage;         // Set true if not used as a library
    friend class FindUndef;
    bool      greedyUnbound;        //If set, then variables will be greedily unbounded (set to l_Undef)
    RestartType fixRestartType;     // If set, the solver will always choose the given restart strategy
    GaussianConfig gaussconfig;
    

    enum { polarity_true = 0, polarity_false = 1, polarity_rnd = 3, polarity_auto = 4};

    // Statistics: (read-only member variable)
    //
    uint64_t starts, dynStarts, staticStarts, fullStarts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t clauses_literals, learnts_literals, max_literals, tot_literals;
    uint64_t nbDL2, nbBin, lastNbBin, becameBinary, lastSearchForBinaryXor, nbReduceDB;
    uint64_t improvedClauseNo, improvedClauseSize;

    //Logging
    void needStats();              // Prepares the solver to output statistics
    void needProofGraph();         // Prepares the solver to output proof graphs during solving
    void setVariableName(Var var, char* name); // Sets the name of the variable 'var' to 'name'. Useful for statistics and proof logs (i.e. used by 'logger')
    const vec<Clause*>& get_sorted_learnts(); //return the set of learned clauses, sorted according to the logic used in MiniSat to distinguish between 'good' and 'bad' clauses
    const vec<Clause*>& get_learnts() const; //Get all learnt clauses that are >1 long
    const vector<Lit> get_unitary_learnts() const; //return the set of unitary learnt clauses
    const uint get_unitary_learnts_num() const; //return the number of unitary learnt clauses
    void dumpSortedLearnts(const char* file, const uint32_t maxSize); // Dumps all learnt clauses (including unitary ones) into the file
    void needLibraryCNFFile(const char* fileName); //creates file in current directory with the filename indicated, and puts all calls from the library into the file.

    #ifdef USE_GAUSS
    const uint32_t get_sum_gauss_called() const;
    const uint32_t get_sum_gauss_confl() const;
    const uint32_t get_sum_gauss_prop() const;
    const uint32_t get_sum_gauss_unit_truths() const;
    #endif //USE_GAUSS

    //Printing statistics
    const uint32_t getNumElimSubsume() const; // Get variable elimination stats from Subsumer
    const uint32_t getNumElimXorSubsume() const; // Get variable elimination stats from XorSubsumer
    const uint32_t getNumXorTrees() const; // Get the number of trees built from 2-long XOR-s. This is effectively the number of variables that replace other variables
    const uint32_t getNumXorTreesCrownSize() const; // Get the number of variables being replaced by other variables
    const double getTotalTimeSubsumer() const;
    const double getTotalTimeXorSubsumer() const;
    
protected:
    #ifdef USE_GAUSS
    void print_gauss_sum_stats();
    void clearGaussMatrixes();
    vector<Gaussian*> gauss_matrixes;

    //stats
    uint32_t sum_gauss_called;
    uint32_t sum_gauss_confl;
    uint32_t sum_gauss_prop;
    uint32_t sum_gauss_unit_truths;
    friend class Gaussian;
    #endif //USE_GAUSS
    
    template <class T>
    Clause* addClauseInt(T& ps, uint group);
    template<class T>
    XorClause* addXorClauseInt(T& ps, bool xor_clause_inverted, const uint32_t group);
    template<class T>
    bool addLearntClause(T& ps, const uint group, const uint32_t activity);
    template<class T>
    void    removeWatchedCl(vec<T> &ws, const ClauseOffset c);
    template<class T>
    bool    findWatchedCl(const vec<T>& ws, const ClauseOffset c) const;
    template<class T>
    void    removeWatchedBinCl(vec<T> &ws, const Lit impliedLit);
    template<class T>
    void    removeWatchedBinClAll(vec<T> &ws, const Lit impliedLit);
    template<class T>
    bool    findWatchedBinCl(const vec<T>& ws, const Lit impliedLit) const;
    
    // Helper structures:
    //
    struct VarOrderLt {
        const vec<uint32_t>&  activity;
        bool operator () (Var x, Var y) const {
            return activity[x] > activity[y];
        }
        VarOrderLt(const vec<uint32_t>&  act) : activity(act) { }
    };

    friend class VarFilter;
    struct VarFilter {
        const Solver& s;
        VarFilter(const Solver& _s) : s(_s) {}
        bool operator()(Var v) const {
            return s.assigns[v].isUndef() && s.decision_var[v];
        }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    ClauseAllocator     clauseAllocator;
    vec<Clause*>        clauses;          // List of problem clauses.
    vec<Clause*>        binaryClauses;    // Binary clauses are regularly moved here
    vec<XorClause*>     xorclauses;       // List of problem xor-clauses. Will be freed
    vec<Clause*>        learnts;          // List of learnt clauses.
    vec<XorClause*>     freeLater;        // xor clauses that need to be freed later due to Gauss
    vec<uint32_t>       activity;         // A heuristic measurement of the activity of a variable.
    uint32_t            var_inc;          // Amount to bump next variable with.
    double              cla_inc;          // Amount to bump learnt clause oldActivity with
    vec<vec<Watched> >  watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<vec<ClauseOffset> > xorwatches;   // 'xorwatches[var]' is a list of constraints watching var in XOR clauses.
    vec<vec<WatchedBin> >  binwatches;
    vec<lbool>          assigns;          // The current assignments
    vector<bool>        polarity;         // The preferred polarity of each variable.
    #ifdef USE_OLD_POLARITIES
    vector<bool>        oldPolarity;      // The polarity before the last setting. Good for unsetting polairties that have been changed since the last conflict
    #endif //USE_OLD_POLARITIES
    vector<bool>        decision_var;     // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<uint32_t>       trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<PropagatedFrom> reason;           // 'reason[var]' is the clause that implied the variables current value, or 'NULL' if none.
    vec<int32_t>        level;            // 'level[var]' contains the level at which the assignment was made.
    uint64_t            curRestart;
    uint32_t            nbclausesbeforereduce;
    uint32_t            nbCompensateSubsumer; // Number of learnt clauses that subsumed normal clauses last time subs. was executed
    uint32_t            qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    Lit                 failBinLit;
    uint32_t            simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.
    bqueue<uint>        nbDecisionLevelHistory; // Set of last decision level in conflict clauses
    double              totalSumOfDecisionLevel;
    uint64_t            conflictsAtLastSolve;
    #ifdef RANDOM_LOOKAROUND_SEARCHSPACE
    bqueue<uint>        avgBranchDepth; // Avg branch depth
    #endif //RANDOM_LOOKAROUND_SEARCHSPACE
    MTRand              mtrand;           // random number generaton
    RestartType         restartType;      // Used internally to determine which restart strategy to choose
    RestartType         lastSelectedRestartType; //the last selected restart type
    friend class        Logger;
    #ifdef STATS_NEEDED
    Logger logger;                        // dynamic logging, statistics
    bool                dynamic_behaviour_analysis; // Is logger running?
    #endif
    uint                maxRestarts;      // More than this number of restarts will not be performed

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vector<bool>        seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    
    uint64_t MYFLAG;
    template<class T>
    const uint32_t calcNBLevels(const T& ps);
    vec<uint64_t> permDiff; // LS: permDiff[var] contains the current conflict number... Used to count the number of different decision level variables in learnt clause
    #ifdef UPDATEVARACTIVITY
    vec<Var> lastDecisionLevel;
    #endif

    //Logging
    uint                learnt_clause_group; //the group number of learnt clauses. Incremented at each added learnt clause
    FILE                *libraryCNFFile; //The file that all calls from the library are logged

    // Main internal methods:
    //
    const bool simplify    ();                                                           // Removes already satisfied clauses.
    //int      nbPropagated     (int level);
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (const Lit p, const PropagatedFrom& from = PropagatedFrom());                 // Enqueue a literal. Assumes value of literal is undefined.
    void     uncheckedEnqueueLight (const Lit p);
    bool     enqueue          (Lit p, PropagatedFrom from = PropagatedFrom());                            // Test if fact 'p' contradicts current state, enqueue otherwise.
    PropagatedFrom  propagate (const bool update = true);                         // Perform unit propagation. Returns possibly conflicting clause.
    PropagatedFrom  propagateBin();
    PropagatedFrom  propagateBinNoLearnts();
    template<bool dontCareLearnt>
    PropagatedFrom  propagateBinExcept(const Lit& exceptLit);
    template<bool dontCareLearnt>
    PropagatedFrom  propagateBinOneLevel();
    PropagatedFrom  propagate_xors   (const Lit& p);
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    Clause*  analyze          (PropagatedFrom confl, vec<Lit>& out_learnt, int& out_btlevel, uint32_t &nblevels, const bool update); // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts, int nof_conflicts_fullrestart, const bool update = true);      // Search for a given number of conflicts.
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    llbool   handle_conflict  (vec<Lit>& learnt_clause, PropagatedFrom confl, int& conflictC, const bool update);// Handles the conflict clause
    llbool   new_decision     (const int& nof_conflicts, const int& nof_conflicts_fullrestart, int& conflictC);  // Handles the case when all propagations have been made, and now a decision must be made

    // Maintaining Variable/Clause activity:
    //
    void     claBumpActivity (Clause& c);
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.

    // Operations on clauses:
    //
    void     attachClause     (XorClause& c);
    void     attachClause     (Clause& c);             // Attach a clause to watcher lists.
    void     detachClause     (const XorClause& c);
    void     detachClause     (const Clause& c);       // Detach a clause to watcher lists.
    void     detachModifiedClause(const Lit lit1, const Lit lit2, const uint size, const Clause* address);
    void     detachModifiedClause(const Var var1, const Var var2, const uint origSize, const XorClause* address);
    template<class T>
    void     removeClause(T& c);                       // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    //void     reverse_binary_clause(Clause& c) const;   // Binary clauses --- the first Lit has to be true
    void     testAllClauseAttach() const;
    void     findAllAttach() const;
    const bool findClause(XorClause* c) const;
    const bool findClause(Clause* c) const;

    // Misc:
    //
    uint32_t decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (const Var& x) const; // Used to represent an abstraction of sets of decision levels.
    
    //Xor-finding related stuff
    friend class XorFinder;
    friend class Conglomerate;
    friend class MatrixFinder;
    friend class PartFinder;
    friend class VarReplacer;
    friend class ClauseCleaner;
    friend class RestartTypeChooser;
    friend class FailedVarSearcher;
    friend class Subsumer;
    friend class XorSubsumer;
    friend class PartHandler;
    friend class StateSaver;
    friend class UselessBinRemover;
    friend class OnlyNonLearntBins;
    friend class ClauseAllocator;
    Conglomerate* conglomerate;
    VarReplacer* varReplacer;
    ClauseCleaner* clauseCleaner;
    FailedVarSearcher* failedVarSearcher;
    PartHandler* partHandler;
    Subsumer* subsumer;
    XorSubsumer* xorSubsumer;
    RestartTypeChooser* restartTypeChooser;
    MatrixFinder* matrixFinder;
    const bool chooseRestartType(const uint& lastFullRestart);
    void setDefaultRestartType();
    const bool checkFullRestart(int& nof_conflicts, int& nof_conflicts_fullrestart, uint& lastFullRestart);
    void performStepsBeforeSolve();
    const lbool simplifyProblem(const uint32_t numConfls);
    bool simplifying;

    // Debug & etc:
    void     printLit         (const Lit l) const;
    void     verifyModel      ();
    bool     verifyClauses    (const vec<Clause*>& cs) const;
    bool     verifyXorClauses (const vec<XorClause*>& cs) const;
    void     checkSolution();
    void     checkLiteralCount();
    void     printStatHeader  () const;
    void     printRestartStat ();
    void     printEndSearchStat();
    double   progressEstimate () const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    const bool noLearntBinaries() const;
    
    // Polarity chooser
    void calculateDefaultPolarities(); //Calculates the default polarity for each var, and fills defaultPolarities[] with it
    bool defaultPolarity(); //if polarity_mode is not polarity_auto, this returns the default polarity of the variable
    void tallyVotes(const vec<Clause*>& cs, vector<double>& votes) const;
    void tallyVotes(const vec<XorClause*>& cs, vector<double>& votes) const;
};


//=================================================================================================
// Implementation of inline methods:


inline void Solver::insertVarOrder(Var x)
{
    if (!order_heap.inHeap(x) && decision_var[x]) order_heap.insert(x);
}

inline void Solver::varDecayActivity()
{
    var_inc *= 11;
    var_inc /= 10;
}
inline void Solver::varBumpActivity(Var v)
{
    if ( (activity[v] += var_inc) > (0x1U) << 24 ) {
        //printf("RESCALE!!!!!!\n");
        //std::cout << "var_inc: " << var_inc << std::endl;
        // Rescale:
        for (Var var = 0; var != nVars(); var++) {
            activity[var] >>= 14;
        }
        var_inc >>= 14;
        //var_inc = 1;
        //std::cout << "var_inc: " << var_inc << std::endl;
        
        /*Heap<VarOrderLt> copy_order_heap2(order_heap);
        while(!copy_order_heap2.empty()) {
            Var v = copy_order_heap2.getmin();
            if (decision_var[v])
                std::cout << "var_" << v+1 << " act: " << activity[v] << std::endl;
        }*/
    }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v);
}

inline void Solver::claBumpActivity (Clause& c)
{
    if ( (c.oldActivity() += cla_inc) > 1e20 ) {
        // Rescale:
        for (uint32_t i = 0; i < learnts.size(); i++)
            learnts[i]->oldActivity() *= 1e-17;
        cla_inc *= 1e-20;
    }
}

inline void Solver::claDecayActivity()
{
    //cla_inc *= clause_decay;
}

inline bool     Solver::enqueue         (Lit p, PropagatedFrom from)
{
    return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true);
}
inline bool     Solver::locked          (const Clause& c) const
{
    if (c.size() == 2) return true; //we don't know in this case :I
    PropagatedFrom from(reason[c[0].var()]);
    return !from.isBinary() && from.getClause() == &c && value(c[0]) == l_True;
}
inline void     Solver::newDecisionLevel()
{
    trail_lim.push(trail.size());
    #ifdef VERBOSE_DEBUG
    cout << "New decision level: " << trail_lim.size() << endl;
    #endif
}
/*inline int     Solver::nbPropagated(int level) {
    if (level == decisionLevel())
        return trail.size() - trail_lim[level-1] - 1;
    return trail_lim[level] - trail_lim[level-1] - 1;
}*/
inline uint32_t      Solver::decisionLevel ()      const
{
    return trail_lim.size();
}
inline uint32_t Solver::abstractLevel (const Var& x) const
{
    return 1 << (level[x] & 31);
}
inline lbool    Solver::value         (const Var& x) const
{
    return assigns[x];
}
inline lbool    Solver::value         (const Lit& p) const
{
    return assigns[p.var()] ^ p.sign();
}
inline lbool    Solver::modelValue    (const Lit& p) const
{
    return model[p.var()] ^ p.sign();
}
inline uint32_t      Solver::nAssigns      ()      const
{
    return trail.size();
}
inline uint32_t      Solver::nClauses      ()      const
{
    return clauses.size() + xorclauses.size()+binaryClauses.size();
}
inline uint32_t      Solver::nLiterals      ()      const
{
    return clauses_literals + learnts_literals;
}
inline uint32_t      Solver::nLearnts      ()      const
{
    return learnts.size();
}
inline uint32_t      Solver::nVars         ()      const
{
    return assigns.size();
}
inline void     Solver::setPolarity   (Var v, bool b)
{
    polarity    [v] = (char)b;
}
inline void     Solver::setDecisionVar(Var v, bool b)
{
    decision_var[v] = b;
    if (b) {
        insertVarOrder(v);
    }
}
inline lbool     Solver::solve         ()
{
    vec<Lit> tmp;
    return solve(tmp);
}
inline bool     Solver::okay          ()      const
{
    return ok;
}
inline void     Solver::setSeed (const uint32_t seed)
{
    mtrand.seed(seed);    // Set seed of the variable-selection and clause-permutation(if applicable)
}
#ifdef STATS_NEEDED
inline void     Solver::needStats()
{
    dynamic_behaviour_analysis = true;    // Sets the solver and the logger up to generate statistics
    logger.statistics_on = true;
}
inline void     Solver::needProofGraph()
{
    dynamic_behaviour_analysis = true;    // Sets the solver and the logger up to generate proof graphs during solving
    logger.proof_graph_on = true;
}
inline void     Solver::setVariableName(Var var, char* name)
{
    while (var >= nVars()) newVar();
    if (dynamic_behaviour_analysis)
        logger.set_variable_name(var, name);
} // Sets the varible 'var'-s name to 'name' in the logger
#else
inline void     Solver::setVariableName(Var var, char* name)
{}
#endif

#ifdef USE_GAUSS
inline const uint32_t Solver::get_sum_gauss_unit_truths() const
{
    return sum_gauss_unit_truths;
}

inline const uint32_t Solver::get_sum_gauss_called() const
{
    return sum_gauss_called;
}

inline const uint32_t Solver::get_sum_gauss_confl() const
{
    return sum_gauss_confl;
}

inline const uint32_t Solver::get_sum_gauss_prop() const
{
    return sum_gauss_prop;
}
#endif

inline const uint Solver::get_unitary_learnts_num() const
{
    if (decisionLevel() > 0)
        return trail_lim[0];
    else
        return trail.size();
}
template <class T>
inline void Solver::removeWatchedCl(vec<T> &ws, const ClauseOffset c) {
    uint32_t j = 0;
    for (; j < ws.size() && ws[j].clause != c; j++);
    assert(j < ws.size());
    for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
    ws.pop();
}
template <class T>
inline void Solver::removeWatchedBinCl(vec<T> &ws, const Lit impliedLit) {
    uint32_t j = 0;
    for (; j < ws.size() && ws[j].impliedLit != impliedLit; j++);
    assert(j < ws.size());
    for (; j < ws.size()-1; j++) ws[j] = ws[j+1];
    ws.pop();
}
template <class T>
inline void Solver::removeWatchedBinClAll(vec<T> &ws, const Lit impliedLit) {
    T *i = ws.getData();
    T *j = i;
    for (T* end = ws.getDataEnd(); i != end; i++) {
        if (i->impliedLit != impliedLit)
            *j++ = *i;
    }
    ws.shrink(i-j);
}
template<class T>
inline bool Solver::findWatchedCl(const vec<T>& ws, const ClauseOffset c) const
{
    uint32_t j = 0;
    for (; j < ws.size() && ws[j].clause != c; j++);
    return j < ws.size();
}
template<class T>
inline bool Solver::findWatchedBinCl(const vec<T>& ws, const Lit impliedLit) const
{
    uint32_t j = 0;
    for (; j < ws.size() && ws[j].impliedLit != impliedLit; j++);
    return j < ws.size();
}

/*
inline void Solver::reverse_binary_clause(Clause& c) const {
    if (c.size() == 2 && value(c[0]) == l_False) {
        assert(value(c[1]) == l_True);
        std::swap(c[0], c[1]);
    }
}
*/

/*inline void Solver::calculate_xor_clause(Clause& c2) const {
    if (c2.isXor() && ((XorClause*)&c2)->updateNeeded())  {
        XorClause& c = *((XorClause*)&c2);
        bool final = c.xor_clause_inverted();
        for (int k = 0, size = c.size(); k != size; k++ ) {
            const lbool& val = assigns[c[k].var()];
            assert(val != l_Undef);
            
            c[k] = c[k].unsign() ^ val.getBool();
            final ^= val.getBool();
        }
        if (final)
            c[0] = c[0].unsign() ^ !assigns[c[0].var()].getBool();
        
        c.setUpdateNeeded(false);
    }
}*/

template<class T>
inline void Solver::removeClause(T& c)
{
    detachClause(c);
    clauseAllocator.clauseFree(&c);
}

//=================================================================================================
// Debug + etc:

static inline void logLit(FILE* f, Lit l)
{
    fprintf(f, "%sx%d", l.sign() ? "~" : "", l.var()+1);
}

static inline void logLits(FILE* f, const vec<Lit>& ls)
{
    fprintf(f, "[ ");
    if (ls.size() > 0) {
        logLit(f, ls[0]);
        for (uint32_t i = 1; i < ls.size(); i++) {
            fprintf(f, ", ");
            logLit(f, ls[i]);
        }
    }
    fprintf(f, "] ");
}

static inline const char* showBool(bool b)
{
    return b ? "true" : "false";
}


// Just like 'assert()' but expression will be evaluated in the release version as well.
static inline void check(bool expr)
{
    assert(expr);
}

#ifndef DEBUG_ATTACH
inline void Solver::testAllClauseAttach() const
{
    return;
}
inline void Solver::findAllAttach() const
{
    return;
}
#endif //DEBUG_ATTACH

inline void Solver::uncheckedEnqueueLight(const Lit p)
{
    assigns [p.var()] = boolToLBool(!p.sign());//lbool(!sign(p));  // <<== abstract but not uttermost effecient
    trail.push(p);
}

//=================================================================================================

}; //NAMESPACE MINISAT

#endif //SOLVER_H
