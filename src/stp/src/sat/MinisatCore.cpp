#include "core/Solver.h"
#include "MinisatCore.h"
#include "utils/System.h"
#include "simp/SimpSolver.h"

namespace BEEV
{

  template <class T>
  MinisatCore<T>::MinisatCore(volatile bool& interrupt)
  {
     s = new T(interrupt);
  };

  template <class T>
  MinisatCore<T>::~MinisatCore()
  {
    delete s;
  }

  template <class T>
  bool
  MinisatCore<T>::addClause(const SATSolver::vec_literals& ps) // Add a clause to the solver.
  {
    s->addClause(ps);
  }

  template <class T>
  bool
  MinisatCore<T>::okay() const // FALSE means solver is in a conflicting state
  {
    return s->okay();
  }

  template <class T>
  bool
  MinisatCore<T>::solve() // Search without assumptions.
  {
    if (!s->simplify())
      return false;

    return s->solve();

  }

  template <class T>
  uint8_t
  MinisatCore<T>::modelValue(Var x) const
  {
    return Minisat::toInt(s->modelValue(x));
  }

  template <class T>
  Minisat::Var
  MinisatCore<T>::newVar()
  {
    return s->newVar();
  }

  template <class T>
  int MinisatCore<T>::setVerbosity(int v)
  {
    s->verbosity = v;
  }

    template <class T>
    void MinisatCore<T>::setSeed(int i)
    {
      s->random_seed = i;
    }


  template <class T>
  int MinisatCore<T>::nVars()
  {return s->nVars();}

  template <class T>
  void MinisatCore<T>::printStats()
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
    int MinisatCore<T>::nClauses()
  {
    return s->nClauses();
  }

  template <class T>
    bool MinisatCore<T>::simplify()
  {
    s->simplify();
  }



  // I was going to make SimpSolver and Solver instances of this template.
  // But I'm not so sure now because I don't understand what eliminate() does in the simp solver.
  template class MinisatCore<Minisat::Solver>;
  //template class MinisatCore<Minisat::SimpSolver>;
};
