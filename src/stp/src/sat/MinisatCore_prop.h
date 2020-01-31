/*
 * Wraps around minisat with array propagators
 */
#ifndef MINISATCORE_PROP_H_
#define MINIASTCORE_PROP_H_

#include "SATSolver.h"

namespace Minisat
{
   class MinisatCore_prop;
}

namespace BEEV
{
  template <class T>
  class MinisatCore_prop: public SATSolver
  {
    T * s;

  public:
    MinisatCore_prop(volatile bool& timeout);

    ~MinisatCore_prop();

    bool
    addClause(const vec_literals& ps); // Add a clause to the solver.

    bool
    okay() const; // FALSE means solver is in a conflicting state

    virtual
    bool addArray(int array_id, const SATSolver::vec_literals& i, const SATSolver::vec_literals& v, const Minisat::vec<Minisat::lbool>&, const Minisat::vec<Minisat::lbool> &);


    bool
    solve(); // Search without assumptions.

    virtual uint8_t modelValue(Var x) const;

    virtual Var newVar();

    int setVerbosity(int v);

    int nVars();

    void printStats();

    virtual lbool true_literal() {return ((uint8_t)0);}
    virtual lbool false_literal()  {return ((uint8_t)1);}
    virtual lbool undef_literal()  {return ((uint8_t)2);}

    virtual void setSeed(int i);
  };
}
;

#endif
