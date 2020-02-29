// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#include "ToSAT.h"
#include "../BitBlaster.h"
#include "../../printer/printers.h"
#include <iostream>
#include <fstream>
#include "BBNodeManagerASTNode.h"
#include "../../STPManager/UserDefinedFlags.h"

namespace BEEV
{

  bool isTseitinVariable(const ASTNode& n) {
    if (n.GetKind() == SYMBOL && n.GetType() == BOOLEAN_TYPE) {
      const char * zz = n.GetName();
      if (0 == strncmp("cnf", zz, 3))
        {
          return true;
        }
    }
    return false;
  }

  /* FUNCTION: lookup or create a new MINISAT literal
   * lookup or create new MINISAT Vars from the global MAP
   * _ASTNode_to_SATVar.
   */

  SATSolver::Var
  ToSAT::LookupOrCreateSATVar(SATSolver& newSolver, const ASTNode& n)
  {
    ASTtoSATMap::iterator it;
    SATSolver::Var v;

    //look for the symbol in the global map from ASTNodes to ints. if
    //not found, create a S.newVar(), else use the existing one.
    if ((it = _ASTNode_to_SATVar_Map.find(n)) == _ASTNode_to_SATVar_Map.end())
      {
        v = newSolver.newVar();
        _ASTNode_to_SATVar_Map[n] = v;

        //ASSUMPTION: I am assuming that the newSolver.newVar() call increments v
        //by 1 each time it is called, and the initial value of a
        //SATSolver::Var is 0.

        // Copies the symbol into the map that is used to build the counter example.
        // For boolean we create a vector of size 1.
        if (n.GetKind() == BVGETBIT && n[0].GetKind() == SYMBOL || (n.GetKind() == SYMBOL && !isTseitinVariable(n)))
          {
            const ASTNode& symbol = n.GetKind() == BVGETBIT ? n[0] : n;
            const unsigned index = n.GetKind() == BVGETBIT ? n[1].GetUnsignedConst() : 0;
            const unsigned width = n.GetKind() == BVGETBIT ? symbol.GetValueWidth(): 1;

            if (SATVar_to_SymbolIndex.find(symbol) == SATVar_to_SymbolIndex.end())
              {
                // In the SAT solver these are signed...
                vector<unsigned> vec(width,~((unsigned)0));
                SATVar_to_SymbolIndex.insert(make_pair(symbol, vec));
              }
            assert(index < width);
            assert(SATVar_to_SymbolIndex[symbol].size() > index);

            SATVar_to_SymbolIndex[symbol][index] = v;
          }

        // experimental. Don't add Tseitin variables as decision variables.
        //if (!bm->UserFlags.tseitin_are_decision_variables_flag && isTseitinVariable(n))
          //{
//            newSolver.setDecisionVar(v,false);
  //        }

      }
    else
      v = it->second;
    return v;
  }

  /* FUNCTION: convert ASTClauses to MINISAT clauses and solve.
   * Accepts ASTClauses and converts them to MINISAT clauses. Then
   * adds the newly minted MINISAT clauses to the local SAT instance,
   * and calls solve(). If solve returns unsat, then stop and return
   * unsat. else continue.
   */
  bool ToSAT::toSATandSolve(SATSolver& newSolver,
                            ClauseList& cll,
                            bool final,
                            CNFMgr*& cm,
                            bool add_xor_clauses,
			    bool enable_clausal_abstraction)
  {
	  CountersAndStats("SAT Solver", bm);
    bm->GetRunTimes()->start(RunTimes::SendingToSAT);

    int input_clauselist_size = cll.size();
    if (cll.size() == 0)
      {
        FatalError("toSATandSolve: Nothing to Solve", ASTUndefined);    
      }

    if(bm->UserFlags.random_seed_flag)
      {
	newSolver.setSeed(bm->UserFlags.random_seed);
      }

	ClauseContainer& cc = *cll.asList();
    //Clause for the SATSolver
	SATSolver::vec_literals satSolverClause;

    //iterate through the list (conjunction) of ASTclauses cll
    ClauseContainer::const_iterator i = cc.begin(), iend = cc.end();
    for (int count=0, flag=0; i != iend; i++)
      {
        satSolverClause.clear();
        vector<const ASTNode*>::const_iterator j    = (*i)->begin(); 
        vector<const ASTNode*>::const_iterator jend = (*i)->end();      
        //ASTVec  clauseVec;
        //j is a disjunct in the ASTclause (*i)
        for (; j != jend; j++)
          {         
            ASTNode node = **j;
            //clauseVec.push_back(node);
            bool negate = (NOT == node.GetKind()) ? true : false;
            ASTNode n = negate ? node[0] : node;
            SATSolver::Var v = LookupOrCreateSATVar(newSolver, n);
            Minisat::Lit l = SATSolver::mkLit(v, negate);
            satSolverClause.push(l);
          }

        // ASTNode theClause = bm->CreateNode(OR, clauseVec);
        //      if(flag 
        //         && ASTTrue == CheckBBandCNF(newSolver, theClause))
        //        {
        //          continue;
        //        }
#if defined CRYPTOMINISAT__2
        if(add_xor_clauses)
          {
            newSolver.addXorClause(satSolverClause, false);
          }
        else 
          {
            newSolver.addClause(satSolverClause);
          }
#else
        newSolver.addClause(satSolverClause);
#endif

#if defined CRYPTOMINISAT__2
    newSolver.findNormalXors = false;
    newSolver.doSubsumption = true;
    newSolver.verbosity = 0;
    //newSolver.fixRestartType = static_restart;
    newSolver.doPartHandler = true;
#endif

// 	if(enable_clausal_abstraction && 
// 	   count++ >= input_clauselist_size*CLAUSAL_ABSTRACTION_CUTOFF)
// 	  {
// 	    //Arbitrary adding only x% of the clauses in the hopes of
// 	    //terminating early 
// 	    //      cout << "Percentage clauses added: " 
// 	    //           << percentage << endl;
// 	    bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
// 	    bm->GetRunTimes()->start(RunTimes::Solving);
// 	    newSolver.solve();
// 	    bm->GetRunTimes()->stop(RunTimes::Solving);
// 	    if(!newSolver.okay())
// 	      {
// 		return false;         
// 	      }
// 	    count = 0;
// 	    flag  = 1;
// 	    bm->GetRunTimes()->start(RunTimes::SendingToSAT);
// 	  }

	if (newSolver.okay())
          {
            continue;
          }     
        else
          {
            if(bm->UserFlags.stats_flag)
              newSolver.printStats();
            bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
            cll.deleteJustVectors();
            return false;
          }     
      } // End of For-loop adding the clauses 

    // output a CNF
    // Because we use the SAT solver incrementally, this may ouput little pieces of the
    // CNF that need to be joined together. Nicer would be to read it out of the solver each time.
    	if (bm->UserFlags.output_CNF_flag && true)
    	{
    		ofstream file;
    		stringstream fileName;
    		fileName << "output_" << CNFFileNameCounter++ << ".cnf";
    		file.open(fileName.str().c_str());

    		file << "p cnf " << newSolver.nVars() << " " << cll.size() << endl;
    		i = cc.begin(), iend = cc.end();
    		for (; i != iend; i++)
    		{
    			vector<const ASTNode*>::iterator j = (*i)->begin(), jend =
    					(*i)->end();
    			for (; j != jend; j++)
    			{
    				const ASTNode& node = *(*j);
    	            bool negate = (NOT == node.GetKind()) ? true : false;
    	            ASTNode n = negate ? node[0] : node;

    	            ASTtoSATMap::iterator it =  _ASTNode_to_SATVar_Map.find(n);
    	            assert(it != _ASTNode_to_SATVar_Map.end());

    	            SATSolver::Var v = it->second;

    				if (negate)
    					file << "-" << (v + 1) << " ";
    				else
    					file << (v + 1) << " ";
    			}
    			file << "0" << endl;
    		}
    		file.close();

    	}

    // Free the clause list before SAT solving.
    cll.deleteJustVectors();

    // Remove references to Tseitin variables.
    // Delete the cnf generator.
    if (final)
    {
      ASTVec toDelete;

      ASTtoSATMap::const_iterator it =_ASTNode_to_SATVar_Map.begin();
      for (;it!=_ASTNode_to_SATVar_Map.end();it++)
        {
        ASTNode n = it->first;
        if (!n.IsNull() && isTseitinVariable(n))
          toDelete.push_back(n);
        }

      for (ASTVec::iterator it = toDelete.begin(); it!= toDelete.end();it++)
        _ASTNode_to_SATVar_Map.erase(*it);

      delete cm;
      cm = NULL;
    }


    bm->GetRunTimes()->stop(RunTimes::SendingToSAT);
    bm->GetRunTimes()->start(RunTimes::Solving);    

    newSolver.solve();
    bm->GetRunTimes()->stop(RunTimes::Solving);
    if(bm->UserFlags.stats_flag)
      newSolver.printStats();
    if (newSolver.okay())
      return true;
    else
      return false;
  } //end of toSATandSolve()

  //Bucketize clauses into buckets of size 1,2,...CLAUSAL_BUCKET_LIMIT
  ClauseBuckets * ToSAT::Sort_ClauseList_IntoBuckets(ClauseList * cl, int clause_bucket_size)
  {
    ClauseBuckets * cb = new ClauseBuckets();
    ClauseContainer* cc = cl->asList();

    //Sort the clauses, and bucketize by the size of the clauses
    for(ClauseContainer::iterator it = cc->begin(), itend = cc->end();
        it!=itend; it++)
      {
        ClausePtr cptr = *it;
        int cl_size = cptr->size();
        if(cl_size >= clause_bucket_size)
          {
            cl_size = clause_bucket_size;
          }

        //If no clauses of size cl_size have been seen, then create a
        //bucket for that size
        if(cb->find(cl_size) == cb->end())
          {
            ClauseList * cllist = new ClauseList();
            cllist->push_back(cptr);
            (*cb)[cl_size] = cllist;
          }
        else
          {
            ClauseList * cllist = (*cb)[cl_size];
            cllist->push_back(cptr);
          }
      }

    return cb;
  } //End of SortClauseList_IntoBuckets()

  bool ToSAT::CallSAT_On_ClauseBuckets(SATSolver& SatSolver,
                                       ClauseBuckets * cb, CNFMgr*& cm)
  {
    ClauseBuckets::iterator it = cb->begin();
    ClauseBuckets::iterator itend = cb->end();

    bool sat = false;
    for(int count=1;it!=itend;it++, count++)
      {
        ClauseList *cl = (*it).second;
	    sat = toSATandSolve(SatSolver,*cl, count==cb->size(),cm);

        if(!sat)
          {
            return sat;
          }
      }
    return sat;
  }



  //Call the SAT solver, and check the result before returning. This
  //can return one of 3 values, SOLVER_VALID, SOLVER_INVALID or
  //SOLVER_UNDECIDED
  bool ToSAT::CallSAT(SATSolver& SatSolver,
		  	 const ASTNode& input, bool refinement)
  {
    bm->GetRunTimes()->start(RunTimes::BitBlasting);

    ASTNode BBFormula;
    {
        BBNodeManagerASTNode nm(bm);
        Simplifier simp(bm);
        BitBlaster<ASTNode,BBNodeManagerASTNode> BB(&nm,&simp, bm->defaultNodeFactory,&bm->UserFlags);
    	BBFormula = BB.BBForm(input);
    }

    bm->ASTNodeStats("after bitblasting: ", BBFormula);
    bm->GetRunTimes()->stop(RunTimes::BitBlasting);

    if (bm->UserFlags.output_bench_flag)
    {
		ofstream file;
		stringstream fileName;
		fileName << "output_" << benchFileNameCounter++ << ".bench";
		file.open(fileName.str().c_str());
		printer::Bench_Print(file,BBFormula);
		file.close();
    }

    //  I suspect that we can't use clause buckets with the simplifying solvers
    // (simplifying minisat & Cryptominsat).
    //  Because sometimes simplifying removes a variable that later clauses depend on.
    //  But when I set the clause_bucket_size to 1 for the other solvers, errors down.
    int clause_bucket_size;
    if (bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_SOLVER)
  	  clause_bucket_size=3;
    else
  	  clause_bucket_size=3;

    // The CNFMgr is deleted inside the CallSAT_On_ClauseBuckets,
    // just before the final call to the SAT solver.

    CNFMgr* cm = new CNFMgr(bm);
    ClauseList* cl = cm->convertToCNF(BBFormula);
    ClauseList* xorcl = cm->ReturnXorClauses();

    ClauseBuckets * cb = Sort_ClauseList_IntoBuckets(cl,clause_bucket_size);
    cl->asList()->clear(); // clause buckets now point to the clauses.
    delete cl;
    bool sat = CallSAT_On_ClauseBuckets(SatSolver, cb, cm);

    for (ClauseBuckets::iterator it = cb->begin(); it != cb->end(); it++)
    	delete it->second;
    delete cb;

    if(!sat)
      {
    	xorcl->deleteJustVectors();
    	delete xorcl;
    	if (NULL != cm)
    		delete cm;
    	return sat;
      }

#if defined CRYPTOMINISAT__2
    if(!xorcl->asList()->empty())
      {
        sat = toSATandSolve(SatSolver, *xorcl, true, cm, true,false);
      }
#endif

    delete xorcl;
	if (NULL != cm)
		delete cm;
    return sat;
  }

  //##################################################
  //##################################################

  /*******************************************************************
   * Helper Functions
   *******************************************************************/



#if 0

  // Looks up truth value of ASTNode SYMBOL in MINISAT satisfying
  // assignment.
  ASTNode ToSAT::SymbolTruthValue(SATSolver &newSolver, ASTNode form)
  {
    SATSolver::Var satvar = _ASTNode_to_SATVar_Map[form];
    if (newSolver.model[satvar] == SATSolver::l_False)
      {
        return ASTFalse;
      }
    else
      {
        // True or undefined.
        return ASTTrue;
      }
  }

  // This function is for debugging problems with BitBlast and
  // especially ToCNF. It evaluates the bit-blasted formula in the
  // satisfying assignment.  While doing that, it checks that every
  // subformula has the same truth value as its representative
  // literal, if it has one.  If this condition is violated, it halts
  // immediately (on the leftmost lowest term).  Use CreateSimpForm to
  // evaluate, even though it's expensive, so that we can use the
  // partial truth assignment.
  ASTNode ToSAT::CheckBBandCNF(SATSolver& newSolver, ASTNode form)
  {
    // Clear memo table (in case newSolver has changed).
    CheckBBandCNFMemo.clear();
    // Call recursive version that does the work.
    return CheckBBandCNF_int(newSolver, form);
  } //End of CheckBBandCNF()

  // Recursive body CheckBBandCNF
  ASTNode ToSAT::CheckBBandCNF_int(SATSolver& newSolver, ASTNode form)
  {
    //     cout << "++++++++++++++++" 
    //   << endl 
    //   << "CheckBBandCNF_int form = " 
    //   << form << endl;
    
    ASTNodeMap::iterator memoit = CheckBBandCNFMemo.find(form);
    if (memoit != CheckBBandCNFMemo.end())
      {
        // found it.  Return memoized value.
        return memoit->second;
      }

    ASTNode result; // return value, to memoize.

    Kind k = form.GetKind();
    switch (k)
      {
      case TRUE:
      case FALSE:
        {
          return form;
          break;
        }
      case SYMBOL:
      case BVGETBIT:
        {
          result = SymbolTruthValue(newSolver, form);

          //           cout << "================" 
          //                << endl 
          //                << "Checking BB formula:" 
          //                << form << endl;
          //           cout << "----------------" 
          //                << endl 
          //                << "Result:" << result << endl;
          break;
        }
      default:
        {
          // Evaluate the children recursively.
          ASTVec eval_children;
          ASTVec ch = form.GetChildren();
          ASTVec::iterator itend = ch.end();
          for (ASTVec::iterator it = ch.begin(); it < itend; it++)
            {
              eval_children.push_back(CheckBBandCNF_int(newSolver, *it));
            }
          result = bm->CreateSimpForm(k, eval_children);

          //           cout << "================" 
          //                << endl 
          //                << "Checking BB formula:" << form << endl;
          //           cout << "----------------" 
          //                << endl 
          //                << "Result:" << result << endl;
          
          ASTNode replit_eval;
          // Compare with replit, if there is one.
          ASTNodeMap::iterator replit_it = RepLitMap.find(form);
          if (replit_it != RepLitMap.end())
            {
              ASTNode replit = RepLitMap[form];
              // Replit is symbol or not symbol.
              if (SYMBOL == replit.GetKind())
                {
                  replit_eval = SymbolTruthValue(newSolver, replit);
                }
              else
                {
                  // It's (NOT sym).  Get value of sym and complement.
                  replit_eval = 
                    bm->CreateSimpNot(SymbolTruthValue(newSolver, replit[0]));
                }

              //               cout << "----------------" 
              //                    << endl 
              //                    << "Rep lit: " << replit << endl;
              //               cout << "----------------" 
              //                    << endl 
              //                    << "Rep lit value: " << replit_eval << endl;

              if (result != replit_eval)
                {
                  // Hit the panic button.
                  FatalError("Truth value of BitBlasted formula "\
                             "disagrees with representative literal in CNF.");
                }
            }
          else
            {
              //cout << "----------------" << endl << "No rep lit" << endl;
            }

        }
      }

    return (CheckBBandCNFMemo[form] = result);
  } //end of CheckBBandCNF_int()
#endif
}; //end of namespace BEEV
