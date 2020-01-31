// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TRANSFORM_H
#define TRANSFORM_H

#include "AST.h"
#include "../STPManager/STPManager.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  class Simplifier;

  class ArrayTransformer : boost::noncopyable
  {
  public:

      // These map from array and index to ITE and Symbol.
      struct ArrayRead
      {
        ArrayRead(ASTNode _ite, ASTNode _symbol)
        {
          assert(! _symbol.IsNull());
          assert(_ite.GetValueWidth() == _symbol.GetValueWidth());
          assert ((SYMBOL == _symbol.GetKind() || BVCONST == _symbol.GetKind()));

          ite = _ite;
          symbol = _symbol;
        }

        ASTNode ite;     // if not using refinement this will be the ITE for the read. Otherwise == symbol.
        ASTNode symbol;  // each read is allocated a distinct fresh variable.
        ASTNode index_symbol;  // A symbol constrained to equal the index expression.
      };

      // MAP: This maps from arrays to their indexes.
      // This map is used by the TransformArray()
      // function ,as well as the counter example, and refinement.
      // This map is useful in converting array reads into
      // nested ITE constructs. Suppose there are two array reads in the
      // input Read(A,i) and Read(A,j). Then Read(A,i) is replaced with
      // a symbolic constant, say v1, and Read(A,j) is replaced with the
      // following ITE: ITE(i=j,v1,v2)

      typedef map<ASTNode, ArrayRead> arrTypeMap;
      typedef map<ASTNode, arrTypeMap > ArrType ;
      ArrType arrayToIndexToRead;

  private:

    /****************************************************************
     * Private Typedefs and Data                                    *
     ****************************************************************/

    // Handy defs
    ASTNode ASTTrue, ASTFalse, ASTUndefined;

        
    // Memo table used by the transformer while it is transforming the
    // formulas and terms
    ASTNodeMap* TransformMap;
    
    // Flag for debuggin the transformer
    const bool debug_transform;

    // Ptr to an external simplifier
    Simplifier * simp;

    // Ptr to STPManager
    STPMgr * bm;
    
    // Ptr to class that records the runtimes for various parts of the
    // code
    RunTimes * runTimes;

    NodeFactory *nf;

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/
    
    ASTNode TransformTerm(const ASTNode& inputterm);
    void assertTransformPostConditions(const ASTNode & term, ASTNodeSet& visited);

    ASTNode TransformArrayRead(const ASTNode& term);

    ASTNode TransformFormula(const ASTNode& form);

  public:
    static ASTNode TranslateSignedDivModRem(const ASTNode& in, NodeFactory*nf, STPMgr *bm);

    //fill the arrayname_readindices vector if e0 is a READ(Arr,index)
    //and index is a BVCONST
    void FillUp_ArrReadIndex_Vec(const ASTNode& e0, const ASTNode& e1);


    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/      
    
    // Constructor
    ArrayTransformer(STPMgr * bm, Simplifier* s) : 
      bm(bm), 
      simp(s), 
      debug_transform(0),
      TransformMap(NULL)
    {
      nf = bm->defaultNodeFactory;

      runTimes = bm->GetRunTimes();
      ASTTrue  = bm->CreateNode(TRUE);
      ASTFalse = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    // Takes a formula, transforms it by replacing array reads with
    // variables, and returns the transformed formula
    ASTNode TransformFormula_TopLevel(const ASTNode& form);

    void ClearAllTables(void)
    {
      arrayToIndexToRead.clear();
    }

    void printArrayStats()
    {
      cerr << "Array Sizes:";

      for (ArrType::const_iterator
             iset = arrayToIndexToRead.begin(),
             iset_end = arrayToIndexToRead.end();
           iset != iset_end; iset++)
        {
          cerr << iset->second.size() << " : ";
        }
      cerr << endl;
    }

  }; //end of class Transformer

};//end of namespace
#endif
