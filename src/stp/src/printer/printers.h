/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#ifndef PRINTERS_H_
#define PRINTERS_H_
#include <iostream>
#include <vector>
#include <cstring>

#include "../AST/AST.h"
#include "../AST/ASTKind.h"
#include "../STPManager/STP.h"

namespace printer
{
  ostream& Dot_Print(ostream &os, const BEEV::ASTNode n);

  ostream& C_Print(ostream &os,
                   const BEEV::ASTNode n, const int indentation = 0);
  ostream& PL_Print(ostream &os, 
                    const BEEV::ASTNode& n, int indentation=0);

  void PL_Print1(ostream& os, const ASTNode& n,int indentation, bool letize);


  ostream& Lisp_Print(ostream &os, 
                      const BEEV::ASTNode& n,  int indentation=0);
  ostream& Lisp_Print_indent(ostream &os,  
                             const BEEV::ASTNode& n,int indentation=0);

  // The "PrintBack" functions also define all the variables that are used.
  void SMTLIB1_PrintBack(ostream &os,
                        const BEEV::ASTNode& n );

  void SMTLIB2_PrintBack(ostream &os, const ASTNode& n, bool definately_bv=false);

  ostream& GDL_Print(ostream &os, const BEEV::ASTNode n);
  ostream& GDL_Print(ostream &os, const ASTNode n, string (*annotate)(const ASTNode&));

  ostream& Bench_Print(ostream &os, const ASTNode n);
}

#endif /* PRINTERS_H_ */
