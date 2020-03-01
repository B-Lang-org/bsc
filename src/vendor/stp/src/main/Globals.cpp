/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"

namespace BEEV
{
  enum inputStatus input_status = NOT_DECLARED;

  //Originally just used by the parser, now used elesewhere.
  STP     * GlobalSTP;
  STPMgr  * ParserBM;

  // Used exclusively for parsing.
  Cpp_interface * parserInterface;

  void (*vc_error_hdlr)(const char* err_msg) = NULL;

  // This is reusable empty vector, for representing empty children
  // arrays
  ASTVec _empty_ASTVec;

  //Some constant global vars for the Main function. Once they are
  //set, these globals will remain constants. These vars are not used
  //in the STP library.
  const char * prog = "stp";
  int linenum  = 1;
  const char * usage = "Usage: %s [-option] [infile]\n";
  std::string helpstring = "\n";
}; //end of namespace BEEV
