/**************************************************************************************************
Originally From: Solver.C -- (C) Niklas Een, Niklas Sorensson, 2004
Substantially modified by: Mate Soos (2010)
**************************************************************************************************/

#ifndef SIMPLIFIER_H
#define SIMPLIFIER_H

#include "Solver.h"
#include "Queue.h"
#include "CSet.h"
#include "BitArray.h"
#include <map>
#include <vector>
#include <queue>
using std::vector;
using std::map;
using std::priority_queue;

namespace MINISAT
{
using namespace MINISAT;

class ClauseCleaner;
class OnlyNonLearntBins;

class Subsumer
{
public:

    //Construct-destruct
    Subsumer(Solver& S2);
    ~Subsumer();

    //Called from main
    const bool simplifyBySubsumption(const bool alsoLearnt = false);
    const bool subsumeWithBinaries(OnlyNonLearntBins* onlyNonLearntBins);
    void newVar();

    //Used by cleaner
    void unlinkModifiedClause(vec<Lit>& origClause, ClauseSimp c, const bool detachAndNull);
    void unlinkClause(ClauseSimp cc, Var elim = var_Undef);
    ClauseSimp linkInClause(Clause& cl);
    void linkInAlreadyClause(ClauseSimp& c);
    void updateClause(ClauseSimp c);


    //UnElimination
    void extendModel(Solver& solver2);
    const bool unEliminate(const Var var);


    //Get-functions
    const vec<char>& getVarElimed() const;
    const uint32_t getNumElimed() const;
    const bool checkElimedUnassigned() const;
    const double getTotalTime() const;
    
private:
    
    friend class ClauseCleaner;
    friend class ClauseAllocator;
    
    //Main
    vec<ClauseSimp>        clauses;
    CSet                   learntClauses;
    vec<char>              touched;        // Is set to true when a variable is part of a removed clause. Also true initially (upon variable creation).
    vec<Var>               touched_list;   // A list of the true elements in 'touched'.
    CSet                   cl_touched;     // Clauses strengthened.
    CSet                   cl_added;       // Clauses created.
    vec<vec<ClauseSimp> >  occur;          // 'occur[index(lit)]' is a list of constraints containing 'lit'.
    vec<vec<ClauseSimp>* > iter_vecs;      // Vectors currently used for iterations. Removed clauses will be looked up and replaced by 'Clause_NULL'.
    vec<CSet* >            iter_sets;      // Sets currently used for iterations.
    vec<char>              cannot_eliminate;//

    //Global stats
    Solver& solver;
    vec<char> var_elimed; //TRUE if var has been eliminated
    double totalTime;
    uint32_t numElimed;
    map<Var, vector<Clause*> > elimedOutVar;
    
    // Temporaries (to reduce allocation overhead):
    //
    vec<char>           seen_tmp;       // (used in various places)
    
    
    //Limits
    uint32_t numVarsElimed;
    uint32_t numMaxSubsume1;
    uint32_t numMaxSubsume0;
    uint32_t numMaxElim;
    int64_t numMaxBlockToVisit;
    uint32_t numMaxBlockVars;
    
    //Start-up
    template<bool UseCL>
    void addFromSolver(vec<Clause*>& cs, bool alsoLearnt = false);
    void fillCannotEliminate();
    void clearAll();

    //Finish-up
    void freeMemory();
    void addBackToSolver();
    void removeWrong(vec<Clause*>& cs);
    void removeAssignedVarsFromEliminated();
    
    //Iterations
    void registerIteration  (CSet& iter_set) { iter_sets.push(&iter_set); }
    void unregisterIteration(CSet& iter_set) { remove(iter_sets, &iter_set); }
    void registerIteration  (vec<ClauseSimp>& iter_vec) { iter_vecs.push(&iter_vec); }
    void unregisterIteration(vec<ClauseSimp>& iter_vec) { remove(iter_vecs, &iter_vec); }
    
    // Subsumption:
    void touch(const Var x);
    void touch(const Lit p);
    template<class T>
    void findSubsumed(const T& ps, const uint32_t abst, vec<ClauseSimp>& out_subsumed);
    bool isSubsumed(Clause& ps);
    template<class T>
    uint32_t subsume0(T& ps, uint32_t abs);
    template<class T>
    uint32_t subsume0Orig(const T& ps, uint32_t abs);
    bool subsumedNonLearnt;
    void subsume0BIN(const Lit lit, const vec<char>& lits);
    void subsume1(ClauseSimp& ps);
    void smaller_database();
    void almost_all_database();
    template<class T1, class T2>
    bool subset(const T1& A, const T2& B);
    bool subsetAbst(uint32_t A, uint32_t B);
    
    void orderVarsForElim(vec<Var>& order);
    bool maybeEliminate(Var x);
    void MigrateToPsNs(vec<ClauseSimp>& poss, vec<ClauseSimp>& negs, vec<ClauseSimp>& ps, vec<ClauseSimp>& ns, const Var x);
    void DeallocPsNs(vec<ClauseSimp>& ps, vec<ClauseSimp>& ns);
    bool merge(const Clause& ps, const Clause& qs, const Lit without_p, const Lit without_q, vec<Lit>& out_clause);

    //Subsume with Nonexistent Bins
    const bool subsWNonExistBinsFull(OnlyNonLearntBins* onlyNonLearntBins);
    const bool subsWNonExistBins(const Lit& lit, OnlyNonLearntBins* onlyNonLearntBins);
    template<class T>
    void subsume1Partial(const T& ps);
    uint32_t subsNonExistentNum;
    uint32_t subsNonExistentumFailed;
    bool subsNonExistentFinish;
    double subsNonExistentTime;
    uint32_t subsNonExistentLitsRemoved;
    vec<Clause*> addBinaryClauses;
    uint32_t doneNum;
    vec<ClauseSimp> subsume1PartialSubs;
    vec<Lit> subsume1PartialQs;
    vec<Lit> toVisit;
    vec<char> toVisitAll;
    vec<Lit> ps2;
    
    class VarOcc {
        public:
            VarOcc(const Var& v, const uint32_t num) :
                var(v)
                , occurnum(num)
            {}
            Var var;
            uint32_t occurnum;
    };
    
    struct MyComp {
        const bool operator() (const VarOcc& l1, const VarOcc& l2) const {
            return l1.occurnum > l2.occurnum;
        }
    };
    
    void blockedClauseRemoval();
    const bool allTautology(const vec<Lit>& ps, const Lit lit);
    uint32_t numblockedClauseRemoved;
    const bool tryOneSetting(const Lit lit, const Lit negLit);
    priority_queue<VarOcc, vector<VarOcc>, MyComp> touchedBlockedVars;
    vec<bool> touchedBlockedVarsBool;
    void touchBlockedVar(const Var x);
    double blockTime;
    
    
    //validity checking
    void verifyIntegrity();
    
    uint32_t clauses_subsumed;
    uint32_t literals_removed;
    uint32_t origNClauses;
    uint32_t numCalls;
    bool fullSubsume;
    uint32_t clauseID;
};

template <class T, class T2>
void maybeRemove(vec<T>& ws, const T2& elem)
{
    if (ws.size() > 0)
        removeW(ws, elem);
}

inline void Subsumer::touch(const Var x)
{
    if (!touched[x]) {
        touched[x] = 1;
        touched_list.push(x);
    }
}

inline void Subsumer::touchBlockedVar(const Var x)
{
    if (!touchedBlockedVarsBool[x]) {
        touchedBlockedVars.push(VarOcc(x, occur[Lit(x, false).toInt()].size()*occur[Lit(x, true).toInt()].size()));
        touchedBlockedVarsBool[x] = 1;
    }
}

inline void Subsumer::touch(const Lit p)
{
    touch(p.var());
}

inline bool Subsumer::subsetAbst(uint32_t A, uint32_t B)
{
    return !(A & ~B);
}

// Assumes 'seen' is cleared (will leave it cleared)
template<class T1, class T2>
bool Subsumer::subset(const T1& A, const T2& B)
{
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].toInt()] = 1;
    for (uint32_t i = 0; i != A.size(); i++) {
        if (!seen_tmp[A[i].toInt()]) {
            for (uint32_t i = 0; i != B.size(); i++)
                seen_tmp[B[i].toInt()] = 0;
            return false;
        }
    }
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].toInt()] = 0;
    return true;
}

inline void Subsumer::newVar()
{
    occur       .push();
    occur       .push();
    seen_tmp    .push(0);       // (one for each polarity)
    seen_tmp    .push(0);
    touched     .push(1);
    var_elimed  .push(0);
    touchedBlockedVarsBool.push(0);
    cannot_eliminate.push(0);
}

inline const vec<char>& Subsumer::getVarElimed() const
{
    return var_elimed;
}

inline const uint32_t Subsumer::getNumElimed() const
{
    return numElimed;
}

inline const double Subsumer::getTotalTime() const
{
    return totalTime;
}

}; //NAMESPACE MINISAT

#endif //SIMPLIFIER_H
