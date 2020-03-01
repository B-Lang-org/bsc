/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "UsefulDefs.h"
#include "../STPManager/STPManager.h"
#include "../main/Globals.h"
namespace BEEV
{
  ostream &operator<<(ostream &os, const Spacer &sp)
  {
    // Instead of wrapping lines with hundreds of spaces, prints
    // a "+" at the beginning of the line for each wrap-around.
    // so lines print like: +14+                (XOR ...
    int blanks = sp._spaces % 60;
    int wraps = sp._spaces / 60;
    if (wraps > 0)
      {
        os << "+" << wraps;
      }
    for (int i = 0; i < blanks; i++)
      os << " ";
    return os;
  }

  //this function accepts the name of a function (as a char *), and
  //records some stats about it. if the input is "print_func_stats",
  //the function will then print the stats that it has collected.
  void CountersAndStats(const char * functionname, STPMgr * bm)
  {
    static function_counters s;
    if (bm->UserFlags.stats_flag)
      {

        if (!strcmp(functionname, "print_func_stats"))
          {
            cout << endl;
            for (function_counters::iterator 
                   it = s.begin(), itend = s.end(); 
                 it != itend; it++)
              cout << "Number of times the function: " 
                   << it->first 
                   << ": is called: " 
                   << it->second << endl;
            return;
          }
        s[functionname] += 1;

      }
  }
}
;// end of namespace
