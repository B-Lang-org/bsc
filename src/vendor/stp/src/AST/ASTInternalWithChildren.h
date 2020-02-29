#ifndef ASTINTERNALWithChildren_H
#define ASTINTERNALWithChildren_H

/*
 * Leaf objects like Symbols and BVConsts don't need a vector of
 * children. On a 64-bit machine, a vector object is 24 bytes. So
 * splitting the two objects apart saves 24 bytes for those objects.
 */

namespace BEEV
{
  class ASTInternalWithChildren : public ASTInternal
  {

  protected:
    // The vector of children
    ASTVec _children;

    /// todo. This should be a bitfield in a superclass if it can fit without increasing the sizeof..
    mutable bool is_simplified;

  public:

    virtual ASTVec const &GetChildren() const
    {
      return _children;
    }

    bool isSimplified() const
    {
      return is_simplified;
    }

    void hasBeenSimplified() const
    {
      is_simplified =true;
    }

    // Constructor (kind and children).
    ASTInternalWithChildren(Kind kind, const ASTVec &children, int nodenum = 0) :
      ASTInternal(kind,nodenum), _children(children)
    {
      is_simplified = false;
    }

    // Constructor (kind only, empty children, int nodenum)
    ASTInternalWithChildren(Kind kind, int nodenum = 0) :
      ASTInternal(kind,nodenum)
    {
      is_simplified = false;
    }
  }; //End of Class ASTInternalBase
}; //end of namespace
#endif
