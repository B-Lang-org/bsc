// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef AST_H
#define AST_H
#include "UsefulDefs.h"
#include "ASTNode.h"
#include "ASTInternal.h"
#include "ASTInterior.h"
#include "ASTSymbol.h"
#include "ASTBVConst.h"

namespace BEEV
{
  void process_argument(const char ch, STPMgr  *bm);
  void FatalError(const char * str, const ASTNode& a, int w = 0) __attribute__ ((noreturn));
  void FatalError(const char * str) __attribute__ ((noreturn));
  void SortByExprNum(ASTVec& c);
  void SortByArith(ASTVec& c);
  bool exprless(const ASTNode n1, const ASTNode n2);
  bool arithless(const ASTNode n1, const ASTNode n2);
  bool isAtomic(Kind k);
  bool isCommutative(const Kind k);
  bool containsArrayOps(const ASTNode&n);
  bool  numberOfReadsLessThan(const ASTNode&n, int v);

  // If (a > b) in the termorder, then return 1 elseif (a < b) in the
  // termorder, then return -1 else return 0
  int TermOrder(const ASTNode& a, const ASTNode& b);
    
  
  //FUNCTION TypeCheck: Assumes that the immediate Children of the
  //input ASTNode have been typechecked. This function is suitable
  //in scenarios like where you are building the ASTNode Tree, and
  //you typecheck as you go along. It is not suitable as a general
  //typechecker
  
  // NB: The boolean value is always true!
  bool BVTypeCheck(const ASTNode& n);
  
 long getCurrentTime();

  ASTVec FlattenKind(Kind k, const ASTVec &children);

  // Checks recursively all the way down.
  bool BVTypeCheckRecursive(const ASTNode& n);

  //Takes a BVCONST and returns its constant value
  unsigned int GetUnsignedConst(const ASTNode n);

  typedef HASHMAP<
    ASTNode, 
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeMap;

  typedef HASHMAP<
    ASTNode, 
    int32_t, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeCountMap;

  typedef HASHSET<
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeSet;

  typedef HASHMULTISET<
    ASTNode, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeMultiSet;

  typedef HASHMAP<
    ASTNode, 
    ASTVec, 
    ASTNode::ASTNodeHasher, 
    ASTNode::ASTNodeEqual> ASTNodeToVecMap;

  //Needed for defining the MAP below
  struct ltint
  {
    bool operator()(int s1, int s2) const
    {
      return s1 < s2;
    }
  };

  class ClauseList;

  //Datatype for ClauseLists
  typedef MAP<
    int,
    ClauseList *,
    ltint> ClauseBuckets;

  typedef MAP<
    int,
    ASTVec *,
    ltint> IntToASTVecMap;

  // Function to dump contents of ASTNodeMap
  ostream &operator<<(ostream &os, const ASTNodeMap &nmap);

  void buildListOfSymbols(const ASTNode& n, ASTNodeSet& visited,ASTNodeSet& symbols);
}; // end namespace BEEV
#endif
