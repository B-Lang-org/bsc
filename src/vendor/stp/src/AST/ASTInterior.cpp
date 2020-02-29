// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "AST.h"
#include "../STPManager/STP.h"
namespace BEEV
{
  /******************************************************************
   * ASTInterior Member Functions                                   *
   ******************************************************************/
  
  // Call this when deleting a node that has been stored in the
  // the unique table
  void ASTInterior::CleanUp()
  {
    (ParserBM)->_interior_unique_table.erase(this);
    delete this;
  } //End of Cleanup()

  // Returns kinds.  "lispprinter" handles printing of parenthesis
  // and childnodes. (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  void ASTInterior::nodeprint(ostream& os, bool c_friendly)
  {
    os << _kind_names[_kind];
  } //end of nodeprint()
  
  /******************************************************************
   * ASTInteriorHasher and ASTInteriorEqual Member Functions        *
   ******************************************************************/

  //ASTInteriorHasher operator()
  size_t 
  ASTInterior::ASTInteriorHasher::
  operator()(const ASTInterior *int_node_ptr) const
  {
    size_t hashval = ((size_t) int_node_ptr->GetKind());
    const ASTVec &ch = int_node_ptr->GetChildren();
    ASTVec::const_iterator iend = ch.end();
    for (ASTVec::const_iterator i = ch.begin(); i != iend; i++)
      {
        hashval += i->Hash();
        hashval += (hashval << 10);
        hashval ^= (hashval >> 6);
      }
    
    hashval += (hashval << 3);
    hashval ^= (hashval >> 11);
    hashval += (hashval << 15);
    return hashval;     
  } //End of ASTInteriorHasher operator()
  
  //ASTInteriorEqual operator()
  bool 
  ASTInterior::ASTInteriorEqual::
  operator()(const ASTInterior *int_node_ptr1, 
             const ASTInterior *int_node_ptr2) const
  {
    return (*int_node_ptr1 == *int_node_ptr2);
  } ///End of ASTInteriorEqual operator()
  
}; //end of namespace
