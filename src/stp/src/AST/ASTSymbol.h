// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef ASTSYMBOL_H
#define ASTSYMBOL_H

namespace BEEV
{
  unsigned long long hash(unsigned char *str);

  /******************************************************************
   *  Class ASTSymbol:                                              *
   *                                                                *
   *  Class to represent internals of Symbol node.                  *
   ******************************************************************/
  class ASTSymbol : public ASTInternal
  {
    friend class STPMgr;
    friend class ASTNode;
    friend class ASTNodeHasher;
    friend class ASTNodeEqual;

    const static ASTVec empty_children;

  private:
    /****************************************************************
     * Private Data                                                 *
     ****************************************************************/

    // The name of the symbol
    const char * const _name;

    /****************************************************************
     * Class ASTSymbolHasher:                                       *
     *                                                              *
     * Hasher for ASTSymbol nodes                                   *
     ****************************************************************/
    class ASTSymbolHasher
    {
    public:
      size_t operator()(const ASTSymbol *sym_ptr) const
      {
#ifdef TR1_UNORDERED_MAP
        tr1::hash<string> h;
#else
        //hash<char *> h;
#endif
        //return h(sym_ptr->_name);
        //cerr << "ASTSymbol hasher recieved name: " 
        //<< sym_ptr->_name << endl;
        return (size_t)hash((unsigned char*)(sym_ptr->_name));
      };
    }; // End of class ASTSymbolHasher

    /****************************************************************
     * Class ASTSymbolEqual:                                        *
     *                                                              *
     * Equality for ASTSymbol nodes                                 *
     ****************************************************************/
    class ASTSymbolEqual
    {
    public:
      bool operator()(const ASTSymbol *sym_ptr1, 
                      const ASTSymbol *sym_ptr2) const
      {
        return (*sym_ptr1 == *sym_ptr2);
      }
    }; // End of class ASTSymbolEqual
    
    // comparator
    friend bool operator==(const ASTSymbol &sym1, 
                           const ASTSymbol &sym2)
    {
      return (strcmp(sym1._name, sym2._name) == 0);
    }

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/

    // Get the name of the symbol
    const char * GetName() const;
    
    // Print function for symbol -- return name. (c_friendly is for
    // printing hex. numbers that C compilers will accept)
    virtual void nodeprint(ostream& os, bool c_friendly = false);

    // Call this when deleting a node that has been stored in the the
    // unique table
    virtual void CleanUp();

  public:

    virtual ASTVec const &GetChildren() const
        {
          return empty_children;
        }


    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/


    // Constructor.  This does NOT copy its argument.
    ASTSymbol(const char * const name) :
      ASTInternal(SYMBOL), _name(name)
    {
    }

    // Destructor (does nothing, but is declared virtual here.
    virtual ~ASTSymbol()
    {
    }

    // Copy constructor
    ASTSymbol(const ASTSymbol &sym) :
      ASTInternal(sym._kind), _name(sym._name)
    {
      //printf("inside ASTSymbol constructor %s\n", _name);
    }
  }; //End of ASTSymbol
}; //end of namespace
#endif
