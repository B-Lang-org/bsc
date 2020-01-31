// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef ASTNODE_H
#define ASTNODE_H
#include "NodeFactory/HashingNodeFactory.h"

/********************************************************************
 *  This file gives the class description of the ASTNode class      *
 ********************************************************************/
namespace BEEV 
{
  /******************************************************************
   *  Class ASTNode:                                                *
   *                                                                *
   *  A Kind of Smart pointer to actual ASTInternal datastructure.  *
   *  This class defines the node datastructure for the DAG that    *
   *  captures input formulas to STP.                               *
   ******************************************************************/

  class ASTNode
  {
    friend class STPMgr;
    friend class CNFMgr;
    friend class ASTInterior;
    friend class vector<ASTNode>;
    friend BEEV::ASTNode HashingNodeFactory::CreateNode(const Kind kind,	const BEEV::ASTVec & back_children);
    friend bool exprless(const ASTNode n1, const ASTNode n2);
    friend bool arithless(const ASTNode n1, const ASTNode n2);

  private:
    /****************************************************************
     * Private Data                                                 *
     ****************************************************************/

    // Ptr to the read data
    ASTInternal * _int_node_ptr;

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/

    // Constructor.
    ASTNode(ASTInternal *in);

    //Equal iff ASTIntNode pointers are the same.
    friend bool operator==(const ASTNode& node1, const ASTNode& node2)
    {
      return 
        ((size_t) node1._int_node_ptr) == 
        ((size_t) node2._int_node_ptr);
    }

    friend bool operator!=(const ASTNode& node1, const ASTNode& node2)
    {
      return !(node1 == node2);
    }

    friend bool operator<(const ASTNode& node1, const ASTNode& node2)
    {
      return 
        ((size_t) node1._int_node_ptr) < 
        ((size_t) node2._int_node_ptr);
    }

  public:
    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    uint8_t getIteration() const;
    void setIteration(uint8_t v) const;

    // Default constructor.
    ASTNode() :_int_node_ptr(NULL) {};

    // Copy constructor
    ASTNode(const ASTNode &n);

    // Destructor
    ~ASTNode();

    // Print the arguments in lisp format
    friend ostream &LispPrintVec(ostream &os, 
                                 const ASTVec &v, 
                                 int indentation = 0);

    // Print the arguments in lisp format
    friend ostream &LispPrintVecSpecial(ostream &os, 
                                        const vector<const ASTNode*> &v, 
                                        int indentation = 0);

    // Check if it points to a null node
    inline bool IsNull() const 
    { 
      return _int_node_ptr == NULL;
    }

    bool isConstant() const
    {
    	const Kind k = GetKind();
    	return (k == BVCONST || k == TRUE || k == FALSE);
    }

    bool isSimplfied() const;

    void hasBeenSimplfied() const;


    bool isITE() const
	{
		bool result;

		Kind k = GetKind();
		switch (k)
		{
		case ITE:
		{
			result = true;
			break;
		}
		default:
		{
			result = false;
			break;
		}
		}

		return result;
	}

    bool isAtom() const
    {
      bool result;

      const Kind k = GetKind();
      switch (k)
        {
        case TRUE:
          {
            result = true;
            break;
          }
        case FALSE:
          {
            result = true;
            break;
          }
        case SYMBOL:
          {
            result = true;
            break;
          }
        case BVCONST:
          {
            result = true;
            break;
          }
        default:
          {
            result = false;
            break;
          }
        }

      return result;
    } //End of isAtom()

    bool isPred() const
    {
      bool result;

      const Kind k = GetKind();
      switch (k)
        {
        case BVLT:
          {
            result = true;
            break;
          }
        case BVLE:
          {
            result = true;
            break;
          }
        case BVGT:
          {
            result = true;
            break;
          }
        case BVGE:
          {
            result = true;
            break;
          }
        case BVSLT:
          {
            result = true;
            break;
          }
        case BVSLE:
          {
            result = true;
            break;
          }
        case BVSGT:
          {
            result = true;
            break;
          }
        case BVSGE:
          {
            result = true;
            break;
          }
        case EQ:
          {
            result = true;
            break;
          }
        default:
          {
            result = false;
            break;
          }
        }
      return result;
    } //End of isPred()


    // For lisp DAG printing.  Has it been printed already, so we can
    // just print the node number?
    bool IsAlreadyPrinted() const;
    void MarkAlreadyPrinted() const;

    // delegates to the ASTInternal node.
    void nodeprint(ostream& os, bool c_friendly = false) const;

    // Assignment (for ref counting)
    ASTNode& operator=(const ASTNode& n);

    //Get the STPMgr pointer. FIXME: Currently uses a global
    //ptr. BAD!!
    STPMgr* GetSTPMgr() const;

    // Access node number
    int GetNodeNum() const;

    // Access kind.
    Kind GetKind() const;

    // Access Children of this Node
    const ASTVec &GetChildren() const;

    // Return the number of child nodes
    size_t Degree() const
    {
      return GetChildren().size();
    }
    ;

    // Get indexth childNode.
    const ASTNode& operator[](size_t index) const
    {
      return GetChildren()[index];
    }
    ;

    // Get begin() iterator for child nodes
    ASTVec::const_iterator begin() const
    {
      return GetChildren().begin();
    }
    ;

    // Get end() iterator for child nodes
    ASTVec::const_iterator end() const
    {
      return GetChildren().end();
    }
    ;

    //Get back() element for child nodes
    const ASTNode back() const
    {
      return GetChildren().back();
    }
    ;

    // Get the name from a symbol (char *).  It's an error if kind !=
    // SYMBOL.
    const char * GetName() const;

    //Get the BVCONST value.
    CBV GetBVConst() const;

    unsigned int GetUnsignedConst() const;


    /*******************************************************************
     * ASTNode is of type BV      <==> ((indexwidth=0)&&(valuewidth>0))*
     * ASTNode is of type ARRAY   <==> ((indexwidth>0)&&(valuewidth>0))*
     * ASTNode is of type BOOLEAN <==> ((indexwidth=0)&&(valuewidth=0))*
     *                                                                 *
     * Both indexwidth and valuewidth should never be less than 0      *
     *******************************************************************/
    unsigned int GetIndexWidth() const;
    unsigned int GetValueWidth() const;
    void SetIndexWidth(unsigned int iw) const;
    void SetValueWidth(unsigned int vw) const;
    types GetType(void) const;

    // Hash using pointer value of _int_node_ptr.
    size_t Hash() const
    {
      return (size_t) _int_node_ptr;
    }

    void NFASTPrint(int l, int max, int prefix) const;

    // Lisp-form printer
    ostream& LispPrint(ostream &os, int indentation = 0) const;
    ostream &LispPrint_indent(ostream &os, int indentation) const;

    // Presentation Language Printer
    ostream& PL_Print(ostream &os, int indentation = 0) const;

    // Construct let variables for shared subterms
    void LetizeNode(void) const;

    // Attempt to define something that will work in the gdb
    friend void lp(ASTNode &node);
    friend void lpvec(const ASTVec &vec);

    // Printing to stream
    friend ostream &operator<<(ostream &os, const ASTNode &node)
    {
      node.LispPrint(os, 0);
      return os;
    }
    ;

    // Check if NODE really has a good ptr
    bool IsDefined() const
    {
      return _int_node_ptr != NULL;
    }

    /*****************************************************************
     * Class ASTNodeHahser:                                          *
     *                                                               *
     * Hasher class for STL hash_maps and hash_sets that use ASTNodes*
     * as keys.  Needs to be public so people can define hash tables *
     * (and use ASTNodeMap class)                                    *
     *****************************************************************/
    class ASTNodeHasher
    {
    public:
      size_t operator()(const ASTNode& n) const
      {
        return (size_t) n._int_node_ptr;
        //return (size_t)n.GetNodeNum();
      }
      ;
    }; //End of ASTNodeHasher

    /*****************************************************************
     * Class ASTNodeEqual:                                           *
     *                                                               *
     * Equality for ASTNode hash_set and hash_map. Returns true iff  *
     * internal pointers are the same.  Needs to be public so people *
     * can define hash tables (and use ASTNodeSet class)             *
     *****************************************************************/
    class ASTNodeEqual
    {
    public:
      bool operator()(const ASTNode& n1, const ASTNode& n2) const
      {
        return (n1._int_node_ptr == n2._int_node_ptr);
      }
    }; //End of ASTNodeEqual

  }; //End of Class ASTNode

}; //end of namespace
#endif
