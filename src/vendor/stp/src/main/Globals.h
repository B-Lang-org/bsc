// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef GLOBALS_H
#define GLOBALS_H

#include <iostream>
#include <sstream>
#include <string>
#include <algorithm>
#include <ctime>
#include <unistd.h>
#include <signal.h>
#include <stdio.h>
#include <unistd.h>
#include <vector>

namespace BEEV
{  
  class STPMgr;
  class ASTNode;
  class ASTInternal;
  class ASTInterior;
  class ASTSymbol;
  class ASTBVConst;
  class BVSolver;
  class STP;
  class Cpp_interface;

  /***************************************************************
   * ENUM TYPES
   *
   ***************************************************************/

  enum inputStatus
    {
      NOT_DECLARED =0, // Not included in the input file / stream
      TO_BE_SATISFIABLE,
      TO_BE_UNSATISFIABLE,
      TO_BE_UNKNOWN // Specified in the input file as unknown.
    };
  
  //return types for the GetType() function in ASTNode class
  enum types
    {
      BOOLEAN_TYPE = 0, 
      BITVECTOR_TYPE, 
      ARRAY_TYPE, 
      UNKNOWN_TYPE
    };

  enum SOLVER_RETURN_TYPE 
    {
      SOLVER_INVALID=0, 
      SOLVER_VALID=1, 
      SOLVER_UNDECIDED=2,
      SOLVER_TIMEOUT=3,
      SOLVER_ERROR=-100,
      SOLVER_UNSATISFIABLE = 1,
      SOLVER_SATISFIABLE = 0
    };

  //Empty vector. Useful commonly used ASTNodes
  extern std::vector<ASTNode> _empty_ASTVec;  
  extern ASTNode ASTFalse, ASTTrue, ASTUndefined;

  //Useful global variables. Use for parsing only
  extern  STP * GlobalSTP;
  extern  STPMgr * ParserBM;
  extern Cpp_interface * parserInterface;

  //Some constant global vars for the Main function. Once they are
  //set, these globals will remain constants. These vars are not used
  //in the STP library.
  extern const char * prog;
  extern int linenum;
  extern const char * usage;
  extern std::string helpstring;
  extern const std::string version;
  extern enum inputStatus input_status;


  // Function that computes various kinds of statistics for the phases
  // of STP
  void CountersAndStats(const char * functionname, STPMgr * bm);

}; //end of namespace BEEV

#endif
