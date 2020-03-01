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
  const ASTVec ASTBVConst::astbv_empty_children;

  /****************************************************************
   * ASTBVConst Member Function definitions                       *
   ****************************************************************/

  //Constructor
  ASTBVConst::ASTBVConst(CBV bv, unsigned int width) :
    ASTInternal(BVCONST)
  {
    _bvconst = CONSTANTBV::BitVector_Clone(bv);
    _value_width = width;
    cbv_managed_outside =false;
  } //End of ASTBVConst constructor

  // Copy constructor.
  ASTBVConst::ASTBVConst(const ASTBVConst &sym) :
    ASTInternal(sym._kind)
  {
    _bvconst = CONSTANTBV::BitVector_Clone(sym._bvconst);
    _value_width = sym._value_width;
    cbv_managed_outside =false;
  } //End of copy constructor()

  // Call this when deleting a node that has been stored in the the
  // unique table
  void ASTBVConst::CleanUp()
  {
    (ParserBM)->_bvconst_unique_table.erase(this);
    delete this;
  } //End of Cleanup()

  // Print function for bvconst -- return _bvconst value in bin
  // format (c_friendly is for printing hex. numbers that C
  // compilers will accept)
  void ASTBVConst::nodeprint(ostream& os, bool c_friendly)
  {
    unsigned char *res;
    const char *prefix;
    
    if((GlobalSTP->bm)->UserFlags.print_binary_flag) {
      res = CONSTANTBV::BitVector_to_Bin(_bvconst);
      if (c_friendly)
        {
          prefix = "0b";
        }
      else
        {
          prefix = "0bin";
        }
    }
    else if (_value_width % 4 == 0)
      {
        res = CONSTANTBV::BitVector_to_Hex(_bvconst);
        if (c_friendly)
          {
            prefix = "0x";
          }
        else
          {
            prefix = "0hex";
          }
      }
    else
      {
        res = CONSTANTBV::BitVector_to_Bin(_bvconst);
        if (c_friendly)
          {
            prefix = "0b";
          }
        else
          {
            prefix = "0bin";
          }
      }
    if (NULL == res)
      {
        os << "nodeprint: BVCONST : could not convert to string" << _bvconst;
        FatalError("");
      }
    os << prefix << res;
    CONSTANTBV::BitVector_Dispose(res);
  } //End of nodeprint()

  // Return the bvconst. It is a const-value
  CBV ASTBVConst::GetBVConst() const
  {
    return _bvconst;
  } //End of GetBVConst()

  /****************************************************************
   * Class ASTBVConstHasher and ASTBVConstEqual Functions         *
   ****************************************************************/

  size_t ASTBVConst::ASTBVConstHasher::operator()(const ASTBVConst * bvc) const
  {
    return CONSTANTBV::BitVector_Hash(bvc->_bvconst);
  } //End of ASTBVConstHasher operator


  bool ASTBVConst::ASTBVConstEqual::operator()(const ASTBVConst * bvc1, 
                                               const ASTBVConst * bvc2) const
  {
    if (bvc1->_value_width != bvc2->_value_width)
      {
        return false;
      }
    return (0 == 
            CONSTANTBV::BitVector_Compare(bvc1->_bvconst,
                                          bvc2->_bvconst));
  } //End of ASTBVConstEqual operator
};//End of namespace

