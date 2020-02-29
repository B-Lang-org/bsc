/*
 * Wraps around Cryptominisat minisat.
 */
#ifndef CRYPTOMINISAT_H_
#define CRYPTOMINISAT_H_

#include "SATSolver.h"

namespace MINISAT
{
   class Solver;
}

namespace BEEV
{
  class CryptoMinisat : public SATSolver
  {
    MINISAT::Solver* s;

  public:
    CryptoMinisat();

    ~CryptoMinisat();

    bool
    addClause(const vec_literals& ps); // Add a clause to the solver.

    bool
    okay() const; // FALSE means solver is in a conflicting state


    bool
    solve(); // Search without assumptions.

    virtual uint8_t modelValue(Var x) const;

    virtual Var newVar();

    int setVerbosity(int v);

    int nVars();

    void printStats();

    //nb CMS2 has different literal values to the other minisats.
    virtual lbool true_literal() {return ((uint8_t)1);}
    virtual lbool false_literal()  {return ((uint8_t)-1);}
    virtual lbool undef_literal()  {return ((uint8_t)0);}
  };
}
;

#endif
