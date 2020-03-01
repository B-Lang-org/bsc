// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef USEFULDEFS_H
#define USEFULDEFS_H

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <vector>
#include <iostream>
#include <sstream>
#include <string>
#include <map>
#include <set>
#include <algorithm>
#include <assert.h>

#include "../main/Globals.h"
#include "ASTKind.h"
#include "../extlib-constbv/constantbv.h"
#include "RunTimes.h"

#ifdef EXT_HASH_MAP
#include <ext/hash_set>
#include <ext/hash_map>
#elif defined(TR1_UNORDERED_MAP)
#include <tr1/unordered_map>
#include <tr1/unordered_set>
#define hash_map tr1::unordered_map
#define hash_set tr1::unordered_set
#define hash_multiset tr1::unordered_multiset
#else
#include <hash_set>
#include <hash_map>
#endif

#define MAP          map
#define HASHMAP      hash_map
#define HASHSET      hash_set
#define HASHMULTISET hash_multiset
#define INITIAL_TABLE_SIZE 100

using namespace std;
namespace BEEV {
#ifdef EXT_HASH_MAP
  using namespace __gnu_cxx;
#endif

  /******************************************************************
   * Important classes declared as part of AST datastructures       *
   *                                                                *
   ******************************************************************/
  class STPMgr;
  class ASTNode;
  class ASTInternal;
  class ASTInterior;
  class ASTSymbol;
  class ASTBVConst;
  class BVSolver;

  /******************************************************************
   * Useful typedefs:                                               *
   *                                                                *
   * Vector of ASTNodes, used for child nodes among other things.   *
   * It is good to define hash_map and hash_set in case we want to  *
   * use libraries other than STL.                                  *
   ******************************************************************/
  typedef vector<ASTNode> ASTVec;
  typedef unsigned int * CBV;
  extern ASTVec _empty_ASTVec;

  // Error handling function
  extern void (*vc_error_hdlr)(const char* err_msg);
  
  /******************************************************************
   * Class Spacer: 
   *
   * Spacer class is basically just an int, but the new class allows
   * overloading of << with a special definition that prints the int
   * as that many spaces.
   ******************************************************************/
  class Spacer {
  public:
    int _spaces;
    Spacer(int spaces) 
    { 
      _spaces = spaces; 
    }
    friend ostream& operator<<(ostream& os, const Spacer &ind);
  }; //End of class spacer

  inline Spacer spaces(int width) {
    Spacer sp(width);
    return sp;
  }

  struct eqstr {
    bool operator()(const char* s1, const char* s2) const {
      return strcmp(s1, s2) == 0;
    }
  };

  // function_counters: Table for storing function count stats.
#ifdef TR1_UNORDERED_MAP
  typedef tr1::unordered_map<
    const char*,
    int,
    tr1::hash<const char *>,
    eqstr> function_counters;
#else
  typedef HASHMAP<const char*,
                  int,
                  BEEV::hash<char *>,
                  eqstr> function_counters;
#endif
}; //end of namespace

#endif
