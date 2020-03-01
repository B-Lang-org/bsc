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

/********************************************************************
 *  This file gives the class definitions of the ASTNode class      *
 ********************************************************************/
namespace BEEV 
{
    uint8_t ASTNode::getIteration() const
    {
        return _int_node_ptr->iteration;
    }

    void ASTNode::setIteration(uint8_t v) const
    {
        _int_node_ptr->iteration = v;
    }



    // Constructor;
  //
  // creates a new pointer, increments refcount of pointed-to object.
  ASTNode::ASTNode(ASTInternal *in) :
    _int_node_ptr(in)
  {
    if (in)
      {
        in->IncRef();
      }
  } //End of Constructor

  // Copy constructor.  Maintain _ref_count
  ASTNode::ASTNode(const ASTNode &n) :
    _int_node_ptr(n._int_node_ptr)
  {
    if (n._int_node_ptr)
      {
        n._int_node_ptr->IncRef();
      }
  } //End of Copy Constructor for ASTNode

  // ASTNode accessor function.
  Kind ASTNode::GetKind() const
  {
    //cout << "GetKind: " << _int_node_ptr;
    return _int_node_ptr->GetKind();
  } //End of GetKind()

  // Declared here because of same ordering problem as GetKind.
  const ASTVec &ASTNode::GetChildren() const
  {
    return _int_node_ptr->GetChildren();
  } //End of GetChildren()

  // Access node number
  int ASTNode::GetNodeNum() const
  {
    return _int_node_ptr->_node_num;
  } //End of GetNodeNum()

  unsigned int ASTNode::GetIndexWidth() const
  {
    return _int_node_ptr->_index_width;
  } //End of GetIndexWidth()

  void ASTNode::SetIndexWidth(unsigned int iw) const
  {
    _int_node_ptr->_index_width = iw;
  } //End of SetIndexWidth()

  unsigned int ASTNode::GetValueWidth() const
  {
    return _int_node_ptr->_value_width;
  } //End of GetValueWidth()

  void ASTNode::SetValueWidth(unsigned int vw) const
  {
    _int_node_ptr->_value_width = vw;
  } //End of SetValueWidth()

  //return the type of the ASTNode: 
  //
  // 0 iff BOOLEAN; 1 iff BITVECTOR; 2 iff ARRAY; 3 iff UNKNOWN;
  types ASTNode::GetType() const
  {
    if ((GetIndexWidth() == 0) && (GetValueWidth() == 0)) //BOOLEAN
      return BOOLEAN_TYPE;
    if ((GetIndexWidth() == 0) && (GetValueWidth() > 0)) //BITVECTOR
      return BITVECTOR_TYPE;
    if ((GetIndexWidth() > 0) && (GetValueWidth() > 0)) //ARRAY
      return ARRAY_TYPE;
    return UNKNOWN_TYPE;
  } //End of GetType()

  // Assignment
  ASTNode& ASTNode::operator=(const ASTNode& n)
  {
    if (n._int_node_ptr)
      {
        n._int_node_ptr->IncRef();
      }
    if (_int_node_ptr)
      {
        _int_node_ptr->DecRef();
      }
    _int_node_ptr = n._int_node_ptr;
    return *this;
  } //End of operator=

  // Destructor
  ASTNode::~ASTNode()
  {
    if (_int_node_ptr)
      {
        _int_node_ptr->DecRef();
      }
  } //End of Destructor()

  STPMgr* ASTNode::GetSTPMgr() const
  {
    return ParserBM;
  } //End of GetSTPMgr()

  // Checks if the node has alreadybeen printed or not
  bool ASTNode::IsAlreadyPrinted() const
  {
    STPMgr * bm = GetSTPMgr();
    return (bm->AlreadyPrintedSet.find(*this) != 
            bm->AlreadyPrintedSet.end());
  } //End of IsAlreadyPrinted()

  // Mark the node as printed if it has been already printed
  void ASTNode::MarkAlreadyPrinted() const
  {
    STPMgr * bm = GetSTPMgr();
    bm->AlreadyPrintedSet.insert(*this);
  } //End of MarkAlreadyPrinted()

  // Print the node
  void ASTNode::nodeprint(ostream& os, bool c_friendly) const
  {
    _int_node_ptr->nodeprint(os, c_friendly);
  } //End of nodeprint()

  // Get the name from a symbol (char *).  It's an error if kind !=
  // SYMBOL
  const char * ASTNode::GetName() const
  {
    if (GetKind() != SYMBOL)
      FatalError("GetName: Called GetName on a non-symbol: ", *this);
    return ((ASTSymbol *) _int_node_ptr)->GetName();
  } //End of GetName()

  // Get the value of bvconst from a bvconst.  It's an error if kind
  // != BVCONST Treat the result as const (the compiler can't enforce
  // it).
  CBV ASTNode::GetBVConst() const
  {
    if (GetKind() != BVCONST)
      FatalError("GetBVConst: non bitvector-constant: ", *this);
    return ((ASTBVConst *) _int_node_ptr)->GetBVConst();
  } //End of GetBVConst()

  unsigned int ASTNode::GetUnsignedConst() const
  {
	const ASTNode& n = *this;
    assert(BVCONST == n.GetKind());

    if (sizeof(unsigned int) * 8 < n.GetValueWidth())
      {
        // It may only contain a small value in a bit type,
        // which fits nicely into an unsigned int.  This is
        // common for functions like: bvshl(bv1[128],
        // bv1[128]) where both operands have the same type.
        signed long maxBit = CONSTANTBV::Set_Max(n.GetBVConst());
        if (maxBit >= ((signed long) sizeof(unsigned int)) * 8)
          {
            n.LispPrint(cerr); //print the node so they can find it.
            FatalError("GetUnsignedConst: cannot convert bvconst "\
                       "of length greater than 32 to unsigned int");
          }
      }
    return (unsigned int) *((unsigned int *) n.GetBVConst());
  } //end of GetUnsignedConst




  void ASTNode::NFASTPrint(int l, int max, int prefix) const
  {
    //****************************************
    // stop
    //****************************************
    if (l > max)
      {
        return;
      }

    //****************************************
    // print
    //****************************************
    printf("[%10d]", 0);
    for (int i = 0; i < prefix; i++)
      {
        printf("    ");
      }
    cout << GetKind();
    printf("\n");

    //****************************************
    // recurse
    //****************************************

    const ASTVec &children = GetChildren();
    ASTVec::const_iterator it = children.begin();
    for (; it != children.end(); it++)
      {
        it->NFASTPrint(l + 1, max, prefix + 1);
      }
  } //End of NFASTPrint()

  bool
  ASTNode::isSimplfied() const
  {
    return _int_node_ptr->isSimplified();
  }

  void
  ASTNode::hasBeenSimplfied() const
  {
    _int_node_ptr->hasBeenSimplified();
  }


  //traverse "*this", and construct "let variables" for terms that
  //occur more than once in "*this".
  void ASTNode::LetizeNode(void) const
  {
    Kind kind = this->GetKind();

    if (kind == SYMBOL || kind == BVCONST || kind == FALSE || kind == TRUE)
      return;

    //FIXME: this is ugly.
    STPMgr * bm = GetSTPMgr();
    const ASTVec &c = this->GetChildren();
    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
        ASTNode ccc = *it;
        if (bm->PLPrintNodeSet.find(ccc) == bm->PLPrintNodeSet.end())
          {
            //If branch: if *it is not in NodeSet then,
            //
            //1. add it to NodeSet
            //
            //2. Letize its childNodes

            bm->PLPrintNodeSet.insert(ccc);
            //debugging
            //cerr << ccc;
            ccc.LetizeNode();
          }
        else
          {
            Kind k = ccc.GetKind();
            if (k == SYMBOL || k == BVCONST || k == FALSE || k == TRUE)
              continue;

            //0. Else branch: Node has been seen before
            //
            //1. Check if the node has a corresponding letvar in the
            //1. NodeLetVarMap.
            //
            //2. if no, then create a new var and add it to the
            //2. NodeLetVarMap
            if (bm->NodeLetVarMap.find(ccc) == bm->NodeLetVarMap.end())
              {
                //Create a new symbol. Get some name. if it conflicts with a
                //declared name, too bad.
                int sz = bm->NodeLetVarMap.size();
                ostringstream oss;
                oss << "let_k_" << sz;

                ASTNode CurrentSymbol = bm->CreateSymbol(oss.str().c_str(),this->GetIndexWidth(),this->GetValueWidth());
                /* If for some reason the variable being created here is
                 * already declared by the user then the printed output will
                 * not be a legal input to the system. too bad. I refuse to
                 * check for this.
                 */
                bm->NodeLetVarMap[ccc] = CurrentSymbol;
                std::pair<ASTNode, ASTNode> node_letvar_pair(CurrentSymbol, ccc);
                bm->NodeLetVarVec.push_back(node_letvar_pair);
              }
          }
      }
  } //end of LetizeNode()
};//end of namespace
