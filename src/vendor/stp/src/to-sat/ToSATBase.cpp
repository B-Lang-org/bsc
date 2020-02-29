#include "ToSATBase.h"

namespace BEEV
{

  //This function prints the output of the STP solver
  void ToSATBase::PrintOutput(SOLVER_RETURN_TYPE ret)
  {
    bool true_iff_valid = (SOLVER_VALID == ret);

    if (bm->UserFlags.print_output_flag)
      {
        if (bm->UserFlags.smtlib1_parser_flag || bm->UserFlags.smtlib2_parser_flag)
          {
            if (true_iff_valid &&
                (input_status == TO_BE_SATISFIABLE))
              {
                cerr << "Warning. Expected satisfiable,"\
                  " FOUND unsatisfiable" << endl;
              }
            else if (!true_iff_valid &&
                     (input_status == TO_BE_UNSATISFIABLE))
              {
                cerr << "Warning. Expected unsatisfiable,"\
                  " FOUND satisfiable" << endl;
              }
          }
      }

    if (true_iff_valid)
      {
        bm->ValidFlag = true;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib1_parser_flag || bm->UserFlags.smtlib2_parser_flag)
              cout << "unsat\n";
            else
              cout << "Valid.\n";
          }
      }
    else
      {
        bm->ValidFlag = false;
        if (bm->UserFlags.print_output_flag)
          {
            if (bm->UserFlags.smtlib1_parser_flag || bm->UserFlags.smtlib2_parser_flag)
              cout << "sat\n";
            else
              cout << "Invalid.\n";
          }
      }

    flush(cout);
  } //end of PrintOutput()

}
