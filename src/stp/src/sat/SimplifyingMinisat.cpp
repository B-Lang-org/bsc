#include "SimplifyingMinisat.h"
#include "simp/SimpSolver.h"
#include "utils/System.h"

namespace BEEV
{
  SimplifyingMinisat::SimplifyingMinisat(volatile bool& timeout)
  {
	 s = new Minisat::SimpSolver(timeout);
  }

  SimplifyingMinisat::~SimplifyingMinisat()
  {
    delete s;
  }

  bool
  SimplifyingMinisat::addClause(const vec_literals& ps) // Add a clause to the solver.
  {
    s->addClause(ps);
  }

  bool
  SimplifyingMinisat::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  bool
  SimplifyingMinisat::solve() // Search without assumptions.
  {
    if (!s->simplify())
      return false;

    return s->solve();
  }

  bool
  SimplifyingMinisat::simplify() // Removes already satisfied clauses.
  {
    return s->simplify();
  }

  uint8_t
  SimplifyingMinisat::modelValue(Var x) const
  {
   return Minisat::toInt(s->modelValue(x));
  }

  int SimplifyingMinisat::setVerbosity(int v)
  {
    s->verbosity = v;
  }

  void SimplifyingMinisat::setSeed(int i)
    {
      s->random_seed = i;
    }

  Minisat::Var
  SimplifyingMinisat::newVar()
  {
    return s->newVar();
  }

  int SimplifyingMinisat::nVars()
  {return s->nVars();}

  void SimplifyingMinisat::printStats()
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

  void SimplifyingMinisat::setFrozen(Var x)
  {
      s->setFrozen(x,true);
  }
};
