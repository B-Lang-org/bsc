/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "../mtl/Vec.h"
#include "../mtl/Heap.h"
#include "../mtl/Alg.h"
#include "../utils/Options.h"
#include "../core/SolverTypes.h"
#include <vector>


namespace Minisat {

// Use the GCC extension to use 128-bit indices.
#ifdef INDICES_128BITS
    typedef unsigned int uint128_t __attribute__((mode(TI)));
    static inline uint32_t hash(uint128_t x){ return (uint32_t)x; }
    typedef uint128_t index_type;
#else
    typedef uint64_t index_type;
#endif

#define INDEX_BIT_WIDTH (sizeof(index_type) *8)

//=================================================================================================
// Solver -- the main class:

class Solver_prop {
public:

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //////////////////////////////////////////////////////////////////

    // Changes for the array Propagator...
private:

    struct LessThan_Level {
        Solver_prop* parent;
        LessThan_Level(Solver_prop* parent_)
        {
            parent = parent_;
        }
        bool operator () (const Lit& x, const Lit& y)
        {
            if( parent->value(var(x)) == l_Undef)
                return true;
            if( parent->value(var(y)) == l_Undef)
                return false;

            return parent->level(var(x)) > parent->level(var(y));
        }
    };


	static char printValue(const lbool v) {
		if (v == l_True)
			return '1';
		else if (v == l_False)
			return '0';
		else
			return '.';
	}

	void printClause(const vec<Lit> &c) {
		for (int i = 0; i < c.size(); i++) {
			printf("%s%d:[%c:%d] ", sign(c[i]) ? "-" : "", var(c[i]),
					printValue(value(c[i])), level(var(c[i])));
		}
		printf("\n");
	}

	static void printClause2(const vec<Lit> &c) {
	                for (int i = 0; i < c.size(); i++) {
	                        printf("%s%d ", sign(c[i]) ? "-" : "", var(c[i]) );
	                }
	                printf("\n");
	        }


	struct EqualityVariables
        {
            int my_id;
            int id; // other array id.

	    EqualityVariables()
            {
            }

            EqualityVariables(int me_, int other_)
            {
                my_id = me_;
                id = other_;
                assert(me_ < other_);
            }

            bool
            operator==(const EqualityVariables& other) const
            {
                return other.my_id == my_id && other.id == id;
            }
        };

        struct EqualityVariable_Hash
        {
            uint32_t operator()(const Minisat::Solver_prop::EqualityVariables & e)  const
                { return Minisat::hash(e.my_id + e.id);  }
        };


	struct ArrayAccess
        {
            vec<Lit> index;
            vec<Lit> value;

            int array_id;
            const int id;             // unique id.

	private:
            const int index_size;     // bit-width of the index.
            const int value_size;     // bit-width of the value.

            const bool is_value_constant;    // Whether the value is a constant at the start.
            const bool is_index_constant;

            index_type index_constant;
	public:

            //The index/value is entirely known in advance.
            vec<lbool> constant_index;
            vec<lbool> constant_value;

            // Whether the current object is in the watchlist. To be in the watchlist,
            // the index must be known.
            bool known_index;

            // Used by the watchlist to check whether the index is still unfixed.
            int index_index;

            ArrayAccess(int id_, const vec<Lit>& i, const vec<Lit>& v, const vec<lbool>& ki, const vec<lbool>& kv, int arrayID):
            array_id(arrayID),
            id(id_),
            index_size(std::max(ki.size(), i.size())),
            value_size(std::max(kv.size(), v.size())),
            is_value_constant(kv.size() > 0),
            is_index_constant(ki.size() > 0),
            index_constant(0),
            index_index(0)
            {
                i.copyTo(index);
                v.copyTo(value);
                ki.copyTo(constant_index);
                kv.copyTo(constant_value);

                known_index = false;

                if (is_index_constant)
                    {
                        assert(index_size <=INDEX_BIT_WIDTH);
                        for (int i = 0; i < index_size; i++)
                            {
                                lbool v = constant_index[i];
                                assert(v == l_True || v == l_False);
                                if (v == l_True)
                                    index_constant += (1 << i);
                            }
                    }
            }
            index_type constantIndex() const
             {
                 assert (is_index_constant);
                 return index_constant;
             }

            bool
            isIndexConstant() const
            {
                return is_index_constant;
            }

            bool
            isValueConstant() const
            {
                return is_value_constant;
            }

            int
            indexSize() const
            {
                return index_size;
            }

            int
            valueSize() const
            {
                return value_size;
            }

            void
            print()
            {
                printf("------------\n");

                printf("Index Size: %d\n", index.size());
                printClause2(index);

                printf("Value Size: %d\n", value.size());
                printClause2(value);

                printf("Known Index: %ld ", isIndexConstant() ? index_constant : -1);
                printf("Known Value: %c\n", isValueConstant() ? 't' : 'f');
                printf("Array ID:%d\n", array_id);
                printf("------------\n");
            }
        };

	// We keep the decision level that an index of an array access became fixed.
	// We use this to remove the access from the list of fixed indexes.
	struct ArrayHistory
        {
	    ArrayHistory(ArrayAccess*aa_, int dl)
	    {
	        aa = aa_;
	        decisionLevel =dl;
	    }

            ArrayAccess *aa;
            int decisionLevel;
        };

public:
	// Holds assignments to literals that should be in trail prior to the current decision level.
	struct Assignment
	{
	    Lit l;
	    int decisionLevel;
	    Assignment(Lit l_, int dl)
	    {
	        l =l_;
	        decisionLevel = dl;
	    }
	};
private:

        CRef arrayPropagate(); // top level.

	void eqLitHelper(const Lit& l0, const Lit& l1, const Lit& intermed);
        bool IndexIsSet(const ArrayAccess& iv);

        lbool accessIndex(const ArrayAccess& iv, int i);
	lbool accessValue(const ArrayAccess& iv, int i);
	index_type index_as_int(const ArrayAccess& iv);

	void startWatchOfIndexVariable(ArrayAccess* iv);

	void printClauses();

	void assertIndexesEqual(ArrayAccess &a, ArrayAccess &b);
	CRef writeOutArrayAxiom(ArrayAccess& iv);
	CRef getEqualsLit(ArrayAccess &a, ArrayAccess &b, Lit & eqLit, bool &alreadyCreated);
	CRef addExtraClause(vec<Lit>& l);



        void sortVecByLevel(vec<Lit> & c);
        void sortAlternateTrail();

public:
        bool addArray(int array_id, const vec<Lit>& i, const vec<Lit>& v, const vec<lbool>& ki, const vec<lbool>& kv);
private:

	vec<ArrayAccess* > arrayData; // So we can cleanup.
	int aa_id; // next globally unique id for an array access.
        int last_id; // last id for the array.
        int number_of_arrays;
        int array_trail; // We have checked upto this index in the trail.
        int watched_indexes;
        int top_level_var;
        int alternate_trail_sorted_to;

	Map<index_type, std::vector<ArrayAccess*> >* val_to_aa; // Maps from the index value of fixed indexes to the array accesses.
	Map<Var, std::vector<ArrayAccess*> > watchedLiterals; // The literals that are watched.
	vec<ArrayAccess*> toAddAtStartup;        // These need to be added in at startup.
	vec<ArrayHistory> arrayHistory_stack;    // When the index is fixed it's added into here.
	std::vector<Assignment> alternate_trail; // These literals were assigned below the current decisionLevel.

        Map<EqualityVariables, Lit, EqualityVariable_Hash> equality_variables;

        ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
        //////////////////////////////////////////////////////////////////

public:
    // Constructor/Destructor:
    //
    Solver_prop(volatile bool& timeout);
    virtual ~Solver_prop();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver. 
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver. 
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver. 
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver. 
    bool    addClause_(      vec<Lit>& ps);                     // Add a clause to the solver without making superflous internal copy. Will
                                                                // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    // 
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource contraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory managment:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();

    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //
    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The intitial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

protected:

    // Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
        CRef cref;
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.
    vec<CRef>           learnts;          // List of learnt clauses.
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca;

    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, exept 'seen' wich is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;
    vec<char>           array_of_interest;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource contraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    volatile bool&      asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel ();                                                      // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    void     analyze          (CRef confl, vec<Lit>& out_learnt, int& out_btlevel);    // (bt = backtrack)
    void     analyzeFinal     (Lit p, vec<Lit>& out_conflict);                         // COULD THIS BE IMPLEMENTED BY THE ORDINARIY "analyze" BY SOME REASONABLE GENERALIZATION?
    bool     litRedundant     (Lit p, uint32_t abstract_levels);                       // (helper method for 'analyze()')
    lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Shrink 'cs' to contain only non-satisfied clauses.
    void     rebuildOrderHeap ();

    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.

    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decisionlevel.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }
};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver_prop::reason(Var x) const { return vardata[x].reason; }
inline int  Solver_prop::level (Var x) const { return vardata[x].level; }

inline void Solver_prop::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver_prop::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void Solver_prop::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver_prop::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver_prop::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver_prop::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver_prop::checkGarbage(void){ return checkGarbage(garbage_frac); }
inline void Solver_prop::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); }

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver_prop::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver_prop::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver_prop::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver_prop::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver_prop::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver_prop::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver_prop::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
inline void     Solver_prop::newDecisionLevel()                      { trail_lim.push(trail.size()); }

inline int      Solver_prop::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver_prop::abstractLevel (Var x) const   { return 1 << (level(x) & 31); }
inline lbool    Solver_prop::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver_prop::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver_prop::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver_prop::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }
inline int      Solver_prop::nAssigns      ()      const   { return trail.size(); }
inline int      Solver_prop::nClauses      ()      const   { return clauses.size(); }
inline int      Solver_prop::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver_prop::nVars         ()      const   { return vardata.size(); }
inline int      Solver_prop::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver_prop::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver_prop::setDecisionVar(Var v, bool b)
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline void     Solver_prop::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver_prop::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver_prop::interrupt(){ asynch_interrupt = true; }
inline void     Solver_prop::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver_prop::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver_prop::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interrruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver_prop::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver_prop::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver_prop::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver_prop::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver_prop::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver_prop::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver_prop::okay          ()      const   { return ok; }

inline void     Solver_prop::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver_prop::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver_prop::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver_prop::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }


//=================================================================================================
// Debug etc:


//=================================================================================================
}

#endif
