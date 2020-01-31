#include "CryptoMinisat.h"
#include "utils/System.h"

#undef var_Undef
#undef l_True
#undef l_False
#undef l_Undef


#include "cryptominisat2/Solver.h"
#include "cryptominisat2/SolverTypes.h"

namespace BEEV
{

  CryptoMinisat::CryptoMinisat()
  {
     s = new MINISAT::Solver();
  }

  CryptoMinisat::~CryptoMinisat()
  {
    delete s;
  }

  bool
  CryptoMinisat::addClause(const vec_literals& ps) // Add a clause to the solver.
  {
    // Cryptominisat uses a slightly different vec class.
    // Cryptominisat uses a slightly different Lit class too.

    // VERY SLOW>
    MINISAT::vec<MINISAT::Lit>  v;
    for (int i =0; i<ps.size();i++)
      v.push(MINISAT::Lit(var(ps[i]), sign(ps[i])));

    s->addClause(v);
  }

  bool
  CryptoMinisat::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  bool
  CryptoMinisat::solve() // Search without assumptions.
  {
    return s->solve().getchar();
  }

  uint8_t
  CryptoMinisat::modelValue(Var x) const
  {
    return s->model[x].getchar();
  }

  Minisat::Var
  CryptoMinisat::newVar()
  {
    return s->newVar();
  }

  int CryptoMinisat::setVerbosity(int v)
  {
    s->verbosity = v;
  }

  int CryptoMinisat::nVars()
  {return s->nVars();}

  void CryptoMinisat::printStats()
    {
      double cpu_time = Minisat::cpuTime();
      double mem_used = Minisat::memUsedPeak();
      printf("restarts              : %"PRIu64"\n", s->starts);
      printf("conflicts             : %-12"PRIu64"   (%.0f /sec)\n", s->conflicts   , s->conflicts   /cpu_time);
      printf("decisions             : %-12"PRIu64"   (%4.2f %% random) (%.0f /sec)\n", s->decisions, (float)s->rnd_decisions*100 / (float)s->decisions, s->decisions   /cpu_time);
      printf("propagations          : %-12"PRIu64"   (%.0f /sec)\n", s->propagations, s->propagations/cpu_time);
      printf("conflict literals     : %-12"PRIu64"   (%4.2f %% deleted)\n", s->tot_literals, (s->max_literals - s->tot_literals)*100 / (double)s->max_literals);
      if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
      printf("CPU time              : %g s\n", cpu_time);
    }
};
