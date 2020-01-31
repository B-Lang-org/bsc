// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef CTREXAMPLE_H
#define CTREXAMPLE_H

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/simplifier.h"
#include "../AST/ArrayTransformer.h"
#include "../to-sat/ToSATBase.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  class AbsRefine_CounterExample : boost::noncopyable
  {
  private:

    // Handy defs
    ASTNode ASTTrue, ASTFalse, ASTUndefined;

    // Data structure that holds the counterexample
    ASTNodeMap CounterExampleMap;
            
    // This memo map is used by the ComputeFormulaUsingModel()
    ASTNodeMap ComputeFormulaMap;
      
    // Ptr to STPManager
    STPMgr * bm;
      
    // Ptr to Simplifier
    Simplifier * simp;

    // Ptr to ArrayTransformer
    ArrayTransformer * ArrayTransform;
      
    // Checks if the counterexample is good. In order for the
    // counterexample to be ok, every assert must evaluate to true
    // w.r.t couner_example, and the query must evaluate to
    // false. Otherwise we know that the counter_example is bogus.
    void CheckCounterExample(bool t);

    // Accepts a term and turns it into a constant-term w.r.t
    // counter_example
    ASTNode TermToConstTermUsingModel(const ASTNode& term, 
                                      bool ArrayReadFlag = true);

    ASTNode Expand_ReadOverWrite_UsingModel(const ASTNode& term, 
                                            bool ArrayReadFlag = true);

    void CopySolverMap_To_CounterExample(void);

    //Converts a vector of bools to a BVConst
    ASTNode BoolVectoBVConst(const vector<bool> * w, const unsigned int l);

    //Converts MINISAT counterexample into an AST memotable (i.e. the
    //function populates the datastructure CounterExampleMap)
    void ConstructCounterExample(SATSolver& newS, ToSATBase::ASTNodeToSATVar& satVarToSymbol);

    // Prints MINISAT assigment one bit at a time, for debugging.
    void PrintSATModel(SATSolver& S, ToSATBase::ASTNodeToSATVar& satVarToSymbol);


  public:

    // Constructor
    AbsRefine_CounterExample(STPMgr * b, 
                             Simplifier * s, 
                             ArrayTransformer * at) :
      bm(b), simp(s), ArrayTransform(at)
    {
      ASTTrue  = bm->CreateNode(TRUE);
      ASTFalse = bm->CreateNode(FALSE);
      ASTUndefined = bm->CreateNode(UNDEFINED);
    }

    //Prints the counterexample to stdout
    void PrintCounterExample(bool t, std::ostream& os = cout);
      
    void ClearCounterExampleMap(void)
    {
      CounterExampleMap.clear();
    }

    void ClearComputeFormulaMap(void)
    {
      ComputeFormulaMap.clear();
    }

    //Prints the counterexample to stdout
    void PrintCounterExample_InOrder(bool t);
      
    //queries the counterexample, and returns the value corresponding
    //to e
    ASTNode GetCounterExample(bool t, const ASTNode& e);
      
    //queries the counterexample, and returns a vector of index-value pairs for e
    std::vector<std::pair<ASTNode, ASTNode> > GetCounterExampleArray(bool t, const ASTNode& e);

    int CounterExampleSize(void) const
    {
      return CounterExampleMap.size();
    }

    //FIXME: This is bloody dangerous function. Hack attack to take
    //care of requests from users who want to store complete
    //counter-examples in their own data structures.
    ASTNodeMap GetCompleteCounterExample()
    {
      return CounterExampleMap;
    }
      
    //Computes the truth value of a formula w.r.t counter_example
    ASTNode ComputeFormulaUsingModel(const ASTNode& form);


    /****************************************************************
     * Array Refinement functions                                   *
     ****************************************************************/      
    SOLVER_RETURN_TYPE
    CallSAT_ResultCheck(SATSolver& SatSolver,
                        const ASTNode& modified_input,
                        const ASTNode& original_input,
                        ToSATBase* tosat,
                        bool refinement);

    
    SOLVER_RETURN_TYPE 
    SATBased_ArrayReadRefinement(SATSolver& newS,
                                 const ASTNode& modified_input, 
                                 const ASTNode& original_input,
                                 ToSATBase* tosat);

#if 0
    SOLVER_RETURN_TYPE 
    SATBased_ArrayWriteRefinement(SATSolver& newS,
                                  const ASTNode& orig_input,
                                  ToSATBase *tosat);

    //creates array write axiom only for the input term or formula, if
    //necessary. If there are no axioms to produce then it simply
    //generates TRUE
    ASTNode
    Create_ArrayWriteAxioms(const ASTNode& array_readoverwrite_term,
                            const ASTNode& array_newname);

#endif

    void ClearAllTables(void)
    {
      CounterExampleMap.clear();
      ComputeFormulaMap.clear();
    } //End of ClearAllTables()

    ~AbsRefine_CounterExample()
    {
      ClearAllTables();
    } //End of destructor

  };//End of Class CounterExample

  class CompleteCounterExample : boost::noncopyable
  {
    ASTNodeMap counterexample;
    STPMgr * bv;
  public:
    CompleteCounterExample(ASTNodeMap a, STPMgr* beev) :
      counterexample(a), bv(beev)
    {
    }
    ASTNode GetCounterExample(ASTNode e)
    {
      if (BOOLEAN_TYPE == e.GetType() && SYMBOL != e.GetKind())
        {
          FatalError("You must input a term or propositional variables\n", e);
        }
      if (counterexample.find(e) != counterexample.end())
        {
          return counterexample[e];
        }
      else
        {
          if (SYMBOL == e.GetKind() && BOOLEAN_TYPE == e.GetType())
            {
              return bv->CreateNode(BEEV::FALSE);
            }
              
          if (SYMBOL == e.GetKind())
            {
              ASTNode z = bv->CreateZeroConst(e.GetValueWidth());
              return z;
            }
              
          return e;
        }
    }
  };//end of Class CompleteCounterExample
};//end of namespace
#endif
