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
  const ASTVec ASTSymbol::empty_children;


  /****************************************************************
   * ASTSymbol Member Function definitions                        *
   ****************************************************************/

  // Get the name of the symbol
  const char * ASTSymbol::GetName() const
  {
    return _name;
  }//End of GetName()
  
  // Print function for symbol -- return name. (c_friendly is for
  // printing hex. numbers that C compilers will accept)
  void ASTSymbol::nodeprint(ostream& os, bool c_friendly)
  {
    os << _name;
  } //end of nodeprint()

  // Call this when deleting a node that has been stored in the the
  // unique table
  void ASTSymbol::CleanUp()
  {
    (ParserBM)->_symbol_unique_table.erase(this);
    free((char*) this->_name);
    delete this;
  }//End of cleanup()

  unsigned long long hash(unsigned char *str)
  {
    unsigned long long hash = 5381;
    long long c;

    while ((c = *str++))
      hash = ((hash << 5) + hash) + c; /* hash * 33 + c */

    //cout << "Hash value computed is: " << hash << endl;

    return (unsigned long long)hash;
  }

};//end of namespace
