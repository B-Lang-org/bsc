// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef ASTBVCONST_H
#define ASTBVCONST_H
namespace BEEV
{
  class STPMgr;
  void FatalError(const char * str);

  /******************************************************************
   *  Class ASTBVConst:                                             *
   *                                                                *
   *  Class to represent internals of a bitvector constant          *
   ******************************************************************/
  class ASTBVConst: public ASTInternal
  {
    friend class STPMgr;
    friend class ASTNode;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

  private:
    /****************************************************************
     * Private Data                                                 *
     ****************************************************************/

    //CBV is actually an unsigned*. The bitvector constant is
    //represented using an external library in extlib-bvconst.
    CBV _bvconst;

    // If the CBV is managed outside of this class. Then a defensive copy isn't taken.
    bool cbv_managed_outside;

    /****************************************************************
     * Class ASTBVConstHasher:                                      *
     *                                                              *
     * Hasher for ASTBVConst nodes                                  *
     ****************************************************************/
    class ASTBVConstHasher
    {
    public:
      size_t operator()(const ASTBVConst * bvc) const;
    }; //End of class ASTBVConstHahser
    


    /****************************************************************
     * Class ASTBVConstEqual:                                       *
     *                                                              *
     * Equality for ASTBVConst nodes                                *
     ****************************************************************/
    class ASTBVConstEqual
    {
    public:
      bool operator()(const ASTBVConst * bvc1, 
                      const ASTBVConst * bvc2) const;
    }; //End of class ASTBVConstEqual
      
    /****************************************************************
     * Private Functions (virtual defs and friends)                 *
     ****************************************************************/

    //Constructor
    ASTBVConst(CBV bv, unsigned int width);

    enum CBV_LIFETIME {CBV_MANAGED_OUTSIDE};

    ASTBVConst(CBV bv, unsigned int width, enum CBV_LIFETIME l )
    :  ASTInternal(BVCONST)
    {
      _bvconst = (bv);
      _value_width = width;
      cbv_managed_outside =true;
    }

    // Copy constructor.
    ASTBVConst(const ASTBVConst &sym);  
  
    //friend equality operator
    friend bool operator==(const ASTBVConst &bvc1, const ASTBVConst &bvc2)
    {
      if (bvc1._value_width != bvc2._value_width)
        return false;
      return (0 == CONSTANTBV::BitVector_Compare(bvc1._bvconst, 
                                                 bvc2._bvconst));
    } //End of operator==

    // Call this when deleting a node that has been stored in the the
    // unique table
    virtual void CleanUp();

    // Print function for bvconst -- return _bvconst value in bin
    // format (c_friendly is for printing hex. numbers that C
    // compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false);
    
    const static ASTVec astbv_empty_children;

  public:

    virtual ASTVec const &
    GetChildren() const
    {
      return astbv_empty_children;
    }

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    //Destructor. Call the external destructor
    virtual ~ASTBVConst()
    {
      if (!cbv_managed_outside)
        CONSTANTBV::BitVector_Destroy(_bvconst);
    } //End of destructor

    // Return the bvconst. It is a const-value
    CBV GetBVConst() const;
  }; //End of ASTBVConst  
};//end of namespace
#endif
