// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef STP_H
#define STP_H

#include "../AST/AST.h"
#include "../AST/ArrayTransformer.h"
#include "../STPManager/STPManager.h"
#include "../simplifier/bvsolver.h"
#include "../simplifier/simplifier.h"
#include "../to-sat/ASTNode/ToSAT.h"
#include "../parser/LetMgr.h"
#include "../absrefine_counterexample/AbsRefine_CounterExample.h"
#include "../simplifier/PropagateEqualities.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  class STP  : boost::noncopyable
  {

    

          ASTNode sizeReducing(ASTNode input, BVSolver* bvSolver, PropagateEqualities *pe);

          // A copy of all the state we need to restore to a prior expression.
          struct Revert_to
          {
            ASTNodeMap initialSolverMap; // Map from variables to expressions they were replaced with.
            ASTNode toRevertTo;          // The original expression.
            ArrayTransformer::ArrType backup_arrayToIndexToRead; // array-indices already removed.
          };

          // Accepts query and returns the answer. if query is valid,
          // returns VALID, else returns INVALID. Automatically constructs
          // counterexample for invalid queries, and prints them upon
          // request.
          SOLVER_RETURN_TYPE TopLevelSTPAux(SATSolver& NewSolver,
                                            const ASTNode& modified_input
                                            );


  public:
ArrayTransformer * arrayTransformer;
    
          // calls sizeReducing and the bitblasting simplification.
          ASTNode callSizeReducing(ASTNode simplified_solved_InputToSAT, BVSolver* bvSolver, PropagateEqualities *pe, const int initial_difficulty_score, int & actualBBSize);


    /****************************************************************
     * Public Data:
     *  
     * Absolute toplevel class. No need to make data private
     ****************************************************************/
    STPMgr * bm;
    Simplifier * simp;
    ToSATBase * tosat;
    AbsRefine_CounterExample * Ctr_Example;

    /****************************************************************
     * Constructor and Destructor                                   *
     ****************************************************************/

    //Constructor
    STP(STPMgr* b,
        Simplifier* s,
        ArrayTransformer * a,
        ToSATBase * ts,
        AbsRefine_CounterExample * ce)
    {
      bm   = b;
      simp = s;
      tosat = ts;
      arrayTransformer = a;
      Ctr_Example = ce;
    }// End of constructor


    //Constructor
    STP(STPMgr* b,
        Simplifier* s,
        BVSolver* bsolv,
        ArrayTransformer * a,
        ToSATBase * ts,
        AbsRefine_CounterExample * ce)    
    {
      bm   = b;
      simp = s;
      tosat = ts;
      delete bsolv; // Remove from the constructor later..
      arrayTransformer = a;
      Ctr_Example = ce;
    }// End of constructor

    ~STP()
    {
      ClearAllTables();
      delete Ctr_Example;
      Ctr_Example = NULL;
      delete arrayTransformer;
      arrayTransformer = NULL;
      delete tosat;
      tosat = NULL;
      delete simp;
      simp = NULL;
      //delete bm;
    }

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    // The absolute TopLevel function that invokes STP on the input
    // formula
    SOLVER_RETURN_TYPE TopLevelSTP(const ASTNode& inputasserts, 
                                   const ASTNode& query);

#if 0
    SOLVER_RETURN_TYPE
    UserGuided_AbsRefine(SATSolver& SatSolver,
			 const ASTNode& original_input);
#endif

    void ClearAllTables(void)
    {
		if (simp != NULL)
			simp->ClearAllTables();
		if (arrayTransformer != NULL)
			arrayTransformer->ClearAllTables();
		if (tosat != NULL)
			tosat->ClearAllTables();
		if (Ctr_Example != NULL)
			Ctr_Example->ClearAllTables();
		//bm->ClearAllTables();
	}
  }; //End of Class STP
};//end of namespace
#endif
