/**************************************************************************************************
Originally From: Solver.C -- (C) Niklas Een, Niklas Sorensson, 2004
Substantially modified by: Mate Soos (2010)
**************************************************************************************************/

#ifndef XORSIMPLIFIER_H
#define XORSIMPLIFIER_H

#include "Solver.h"
#include "Vec.h"
#include "XSet.h"

namespace MINISAT
{
using namespace MINISAT;

class ClauseCleaner;

class XorSubsumer
{
public:
    
    XorSubsumer(Solver& S2);
    const bool simplifyBySubsumption(const bool doFullSubsume = false);
    void unlinkModifiedClause(vec<Lit>& origClause, XorClauseSimp c);
    void unlinkModifiedClauseNoDetachNoNULL(vec<Lit>& origClause, XorClauseSimp c);
    void unlinkClause(XorClauseSimp cc, Var elim = var_Undef);
    XorClauseSimp linkInClause(XorClause& cl);
    void linkInAlreadyClause(XorClauseSimp& c);
    void newVar();
    void extendModel(Solver& solver2);
    const uint32_t getNumElimed() const;
    const vec<char>& getVarElimed() const;
    const bool unEliminate(const Var var);
    const bool checkElimedUnassigned() const;
    const double getTotalTime() const;
    
private:
    
    friend class ClauseCleaner;
    friend class ClauseAllocator;
    
    //Main
    vec<XorClauseSimp>        clauses;
    vec<vec<XorClauseSimp> >  occur;          // 'occur[index(lit)]' is a list of constraints containing 'lit'.
    Solver&                   solver;         // The Solver
    
    // Temporaries (to reduce allocation overhead):
    //
    vec<char>                 seen_tmp;       // (used in various places)
    
    //Start-up
    void addFromSolver(vec<XorClause*>& cs);
    void addBackToSolver();
    
    // Subsumption:
    void findSubsumed(XorClause& ps, vec<XorClauseSimp>& out_subsumed);
    bool isSubsumed(XorClause& ps);
    void subsume0(XorClauseSimp ps);
    template<class T1, class T2>
    bool subset(const T1& A, const T2& B);
    bool subsetAbst(uint32_t A, uint32_t B);
    template<class T>
    void findUnMatched(const T& A, const T& B, vec<Lit>& unmatchedPart);

    //helper
    void testAllClauseAttach() const;
    
    //dependent removal
    const bool removeDependent();
    void fillCannotEliminate();
    vec<char> cannot_eliminate;
    void addToCannotEliminate(Clause* it);
    void removeWrong(vec<Clause*>& cs);

    //Global stats
    double totalTime;
    map<Var, vector<XorClause*> > elimedOutVar;
    vec<char> var_elimed;
    uint32_t numElimed;
    
    //Heule-process
    template<class T>
    void xorTwoClauses(const T& c1, const T& c2, vec<Lit>& xored);
    const bool localSubstitute();
    uint32_t localSubstituteUseful;
    
    uint32_t clauses_subsumed;
    uint32_t clauses_cut;
    uint32_t origNClauses;
    uint32_t clauseID;
};

inline bool XorSubsumer::subsetAbst(uint32_t A, uint32_t B)
{
    return !(A & ~B);
}

// Assumes 'seen' is cleared (will leave it cleared)
template<class T1, class T2>
bool XorSubsumer::subset(const T1& A, const T2& B)
{
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].var()] = 1;
    for (uint32_t i = 0; i != A.size(); i++) {
        if (!seen_tmp[A[i].var()]) {
            for (uint32_t i = 0; i != B.size(); i++)
                seen_tmp[B[i].var()] = 0;
            return false;
        }
    }
    for (uint32_t i = 0; i != B.size(); i++)
        seen_tmp[B[i].var()] = 0;
    return true;
}

inline void XorSubsumer::newVar()
{
    occur       .push();
    seen_tmp    .push(0);
    cannot_eliminate.push(0);
    var_elimed.push(0);
}

inline const vec<char>& XorSubsumer::getVarElimed() const
{
    return var_elimed;
}

inline const uint32_t XorSubsumer::getNumElimed() const
{
    return numElimed;
}

inline const double XorSubsumer::getTotalTime() const
{
    return totalTime;
}

}; //NAMESPACE MINISAT

#endif //XORSIMPLIFIER_H
