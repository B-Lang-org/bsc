#include "core_prop/Solver_prop.h"
#include "MinisatCore_prop.h"
#include "utils/System.h"

namespace BEEV
{

  template <class T>
  MinisatCore_prop<T>::MinisatCore_prop(volatile bool& timeout)
  {
     s = new T(timeout);
  };

  template <class T>
  MinisatCore_prop<T>::~MinisatCore_prop()
  {
    delete s;
  }

  template <class T>
  bool
  MinisatCore_prop<T>::addArray(int array_id, const SATSolver::vec_literals& i, const SATSolver::vec_literals& v, const Minisat::vec<Minisat::lbool> & ki, const Minisat::vec<Minisat::lbool> & kv )
  {
	  s->addArray(array_id, i,v, ki,kv);
   return true;
  }


  template <class T>
  bool
  MinisatCore_prop<T>::addClause(const SATSolver::vec_literals& ps) // Add a clause to the solver.
  {
    s->addClause(ps);
  }

  template <class T>
  bool
  MinisatCore_prop<T>::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  template <class T>
  bool
  MinisatCore_prop<T>::solve() // Search without assumptions.
  {
    if (!s->simplify())
      return false;

    return s->solve();

  }

  template <class T>
  uint8_t
  MinisatCore_prop<T>::modelValue(Var x) const
  {
    return Minisat::toInt(s->modelValue(x));
  }

  template <class T>
  Minisat::Var
  MinisatCore_prop<T>::newVar()
  {
    return s->newVar();
  }

  template <class T>
  int MinisatCore_prop<T>::setVerbosity(int v)
  {
    s->verbosity = v;
  }

  template <class T>
  int MinisatCore_prop<T>::nVars()
  {return s->nVars();}

  template <class T>
  void MinisatCore_prop<T>::printStats()
    {
      double cpu_time = Minisat::cpuTime();
      double mem_used = Minisat::memUsedPeak();
      printf("restarts              : %" PRIu64 "\n", s->starts);
      printf("conflicts             : %-12" PRIu64 "   (%.0f /sec)\n", s->conflicts   , s->conflicts   /cpu_time);
      printf("decisions             : %-12" PRIu64 "   (%4.2f %% random) (%.0f /sec)\n", s->decisions, (float)s->rnd_decisions*100 / (float)s->decisions, s->decisions   /cpu_time);
      printf("propagations          : %-12" PRIu64 "   (%.0f /sec)\n", s->propagations, s->propagations/cpu_time);
      printf("conflict literals     : %-12" PRIu64 "   (%4.2f %% deleted)\n", s->tot_literals, (s->max_literals - s->tot_literals)*100 / (double)s->max_literals);
      if (mem_used != 0) printf("Memory used           : %.2f MB\n", mem_used);
      printf("CPU time              : %g s\n", cpu_time);
    }

  template <class T>
  void MinisatCore_prop<T>::setSeed(int i)
  {
    s->random_seed = i;
  }

  template class MinisatCore_prop<Minisat::Solver_prop>;
};
