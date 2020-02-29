#include "cpp_interface.h"

namespace BEEV
{
  // Does some simple caching of prior results.
  void
  Cpp_interface::checkSat(const ASTVec & assertionsSMT2)
  {
    if (ignoreCheckSatRequest)
      return;

    bm.GetRunTimes()->stop(RunTimes::Parsing);

    checkInvariant();
    assert(assertionsSMT2.size() == cache.size());

    Entry& last_run = cache.back();
    if ((last_run.node_number != assertionsSMT2.back().GetNodeNum()) && (last_run.result == SOLVER_SATISFIABLE))
      {
        // extra asserts might have been added to it,
        // flipping from sat to unsat. But never from unsat to sat.
        last_run.result =  SOLVER_UNDECIDED;
      }

    // We might have run this query before, or it might already be shown to be unsat. If it was sat,
    // we've stored the result (but not the model), so we can shortcut and return what we know.
    if (!((last_run.result == SOLVER_SATISFIABLE) || last_run.result == SOLVER_UNSATISFIABLE))
        {
          resetSolver();

          ASTNode query;

          if (assertionsSMT2.size() > 1)
            query = nf->CreateNode(AND, assertionsSMT2);
          else if (assertionsSMT2.size() == 1)
            query = assertionsSMT2[0];
          else
            query = bm.ASTTrue;

          SOLVER_RETURN_TYPE last_result = GlobalSTP->TopLevelSTP(query, bm.ASTFalse);

          // Store away the answer. Might be timeout, or error though..
          last_run = Entry(last_result);
          last_run.node_number = assertionsSMT2.back().GetNodeNum();

          // It's satisfiable, so everything beneath it is satisfiable too.
          if (last_result == SOLVER_SATISFIABLE)
            {
              for (int i = 0; i < cache.size(); i++)
                {
                  assert(cache[i].result != SOLVER_UNSATISFIABLE);
                  cache[i].result = SOLVER_SATISFIABLE;
                }
            }
        }

    if (bm.UserFlags.quick_statistics_flag)
      {
        bm.GetRunTimes()->print();
      }

    (GlobalSTP->tosat)->PrintOutput(last_run.result);
    bm.GetRunTimes()->start(RunTimes::Parsing);
  }
}
;
