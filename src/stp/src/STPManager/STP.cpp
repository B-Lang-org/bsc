// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "STP.h"
#include "DifficultyScore.h"
#include "../to-sat/AIG/ToSATAIG.h"
#include "../simplifier/constantBitP/ConstantBitPropagation.h"
#include "../simplifier/constantBitP/NodeToFixedBitsMap.h"
#include "../sat/SimplifyingMinisat.h"
#include "../sat/MinisatCore.h"
#include "../sat/CryptoMinisat.h"
#include "../sat/MinisatCore_prop.h"
#include "../sat/core_prop/Solver_prop.h"
#include "../simplifier/RemoveUnconstrained.h"
#include "../simplifier/FindPureLiterals.h"
#include "../simplifier/EstablishIntervals.h"
#include "../simplifier/UseITEContext.h"
#include "../simplifier/AlwaysTrue.h"
#include "../simplifier/AIGSimplifyPropositionalCore.h"
#include <memory>

namespace BEEV {

  const  static string cb_message =      "After Constant Bit Propagation. ";
  const  static string bb_message =      "After Bitblast simplification. ";
  const  static string uc_message =      "After Removing Unconstrained. ";
  const  static string int_message =     "After Establishing Intervals. ";
  const  static string pl_message =      "After Pure Literals. ";
  const  static string bitvec_message =  "After Bit-vector Solving. ";
  const  static string size_inc_message= "After Speculative Simplifications. ";
  const  static string pe_message=       "After Propagating Equalities. ";



   // The absolute TopLevel function that invokes STP on the input
    // formula
  SOLVER_RETURN_TYPE STP::TopLevelSTP(const ASTNode& inputasserts, 
				      const ASTNode& query)
  {      

    // Unfortunatey this is a global variable,which the aux function needs to overwrite sometimes.
    bool saved_ack = bm->UserFlags.ackermannisation;

    ASTNode original_input;

    if (query != bm->ASTFalse)
      original_input = bm->CreateNode(AND,
					    inputasserts, 
					    bm->CreateNode(NOT, query));
    else
      original_input = inputasserts;

    SATSolver *newS;
    if (bm->UserFlags.solver_to_use == UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER)
		newS = new SimplifyingMinisat(bm->soft_timeout_expired);
    else if (bm->UserFlags.solver_to_use == UserDefinedFlags::CRYPTOMINISAT_SOLVER)
                    newS = new CryptoMinisat();
    else if (bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_SOLVER)
      newS = new MinisatCore<Minisat::Solver>(bm->soft_timeout_expired);
    else if (bm->UserFlags.solver_to_use == UserDefinedFlags::MINISAT_PROPAGATORS)
      newS = new MinisatCore_prop<Minisat::Solver_prop>(bm->soft_timeout_expired);



    SATSolver& NewSolver = *newS;


    if(bm->UserFlags.stats_flag)
      {
	NewSolver.setVerbosity(1);
      }
    
    if(bm->UserFlags.random_seed_flag)
      {
        NewSolver.setSeed(bm->UserFlags.random_seed);
      }

	SOLVER_RETURN_TYPE result;
    result = TopLevelSTPAux(NewSolver,
			      original_input);

    delete newS;

    bm->UserFlags.ackermannisation =saved_ack;
    return result;

  } //End of TopLevelSTP()
  
  ASTNode
  STP::callSizeReducing(ASTNode simplified_solved_InputToSAT, BVSolver* bvSolver, PropagateEqualities *pe, const int initial_difficulty_score, int & actualBBSize)
  {
    while (true)
      {
        ASTNode last = simplified_solved_InputToSAT;
        simplified_solved_InputToSAT = sizeReducing(last, bvSolver,pe);
        if (last == simplified_solved_InputToSAT)
          break;
      }

    actualBBSize=-1;

    // Expensive, so only want to do it once.
    if (bm->UserFlags.isSet("bitblast-simplification", "1") && initial_difficulty_score < 250000)
      {
        BBNodeManagerAIG bbnm;
        BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&bbnm, simp, bm->defaultNodeFactory , &(bm->UserFlags));
        ASTNodeMap fromTo;
        ASTNodeMap equivs;
        bb.getConsts(simplified_solved_InputToSAT, fromTo,equivs);

        if (equivs.size() > 0)
          {
            /* These nodes have equivalent AIG representations, so even though they have different
             * word level expressions they are identical semantically. So we pick one of the ASTnodes
             * and replace the others with it.
             * TODO: I replace with the lower id node, sometimes though we replace with much more
             * difficult looking ASTNodes.
            */
            ASTNodeMap cache;
            simplified_solved_InputToSAT = SubstitutionMap::replace(simplified_solved_InputToSAT, equivs, cache,bm->defaultNodeFactory,false,true);
            bm->ASTNodeStats(bb_message.c_str(), simplified_solved_InputToSAT);
          }

        if (fromTo.size() > 0)
          {
            ASTNodeMap cache;
            simplified_solved_InputToSAT = SubstitutionMap:: replace(simplified_solved_InputToSAT, fromTo, cache,bm->defaultNodeFactory);
            bm->ASTNodeStats(bb_message.c_str(), simplified_solved_InputToSAT);
          }
        actualBBSize =  bbnm.totalNumberOfNodes();
      }
    return simplified_solved_InputToSAT;
  }


  // These transformations should never increase the size of the DAG.
   ASTNode
  STP::sizeReducing(ASTNode simplified_solved_InputToSAT, BVSolver* bvSolver, PropagateEqualities *pe)
  {

    simplified_solved_InputToSAT = pe->topLevel(simplified_solved_InputToSAT, arrayTransformer);
    if (simp->hasUnappliedSubstitutions())
      {
        simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
        simp->haveAppliedSubstitutionMap();
        bm->ASTNodeStats(pe_message.c_str(), simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.isSet("enable-unconstrained", "1"))
      {
        // Remove unconstrained.
        RemoveUnconstrained r1(*bm);
        simplified_solved_InputToSAT = r1.topLevel(simplified_solved_InputToSAT, simp);
        bm->ASTNodeStats(uc_message.c_str(), simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.isSet("use-intervals", "1"))
      {
        EstablishIntervals intervals(*bm);
        simplified_solved_InputToSAT = intervals.topLevel_unsignedIntervals(simplified_solved_InputToSAT);
        bm->ASTNodeStats(int_message.c_str(), simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.bitConstantProp_flag)
      {
        bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
        simplifier::constantBitP::ConstantBitPropagation cb(simp, bm->defaultNodeFactory, simplified_solved_InputToSAT);
        simplified_solved_InputToSAT = cb.topLevelBothWays(simplified_solved_InputToSAT, true,false);

        bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

        if (cb.isUnsatisfiable())
          simplified_solved_InputToSAT = bm->ASTFalse;

        if (simp->hasUnappliedSubstitutions())
          {
          simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
          simp->haveAppliedSubstitutionMap();
          }

        bm->ASTNodeStats(cb_message.c_str(), simplified_solved_InputToSAT);
      }

    // Find pure literals.
    if (bm->UserFlags.isSet("pure-literals", "1"))
      {
        FindPureLiterals fpl;
        bool changed = fpl.topLevel(simplified_solved_InputToSAT, simp, bm);
        if (changed)
          {
            simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
            simp->haveAppliedSubstitutionMap();
            bm->ASTNodeStats(pl_message.c_str() , simplified_solved_InputToSAT);
          }
      }

    if (bm->UserFlags.isSet("always-true", "0"))
      {
        AlwaysTrue always (simp,bm,bm->defaultNodeFactory);
        simplified_solved_InputToSAT = always.topLevel(simplified_solved_InputToSAT);
        bm->ASTNodeStats("After removing always true: ", simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
      {
        simplified_solved_InputToSAT = bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT, false);
        bm->ASTNodeStats(bitvec_message.c_str(), simplified_solved_InputToSAT);
      }

    return simplified_solved_InputToSAT;
  }

  //Acceps a query, calls the SAT solver and generates Valid/InValid.
  //if returned 0 then input is INVALID if returned 1 then input is
  //VALID if returned 2 then UNDECIDED
  SOLVER_RETURN_TYPE
  STP::TopLevelSTPAux(SATSolver& NewSolver, const ASTNode& original_input)
  {
    bm->ASTNodeStats("input asserts and query: ", original_input);

    DifficultyScore difficulty;
    if (bm->UserFlags.stats_flag)
            cerr << "Difficulty Initially:" << difficulty.score(original_input) << endl;

    // A heap object so I can easily control its lifetime.
    std::auto_ptr<BVSolver> bvSolver(new BVSolver(bm, simp));
    std::auto_ptr<PropagateEqualities> pe (new PropagateEqualities(simp,bm->defaultNodeFactory,bm));

    ASTNode simplified_solved_InputToSAT = original_input;

    // If the number of array reads is small. We rewrite them through.
    // The bit-vector simplifications are more thorough than the array simplifications. For example,
    // we don't currently do unconstrained elimination on arrays--- but we do for bit-vectors.
    // A better way to do this would be to estimate the number of axioms introduced.
    // TODO: I chose the number of reads we perform this operation at randomly.
    bool removed = false;
    if (((bm->UserFlags.ackermannisation && numberOfReadsLessThan(simplified_solved_InputToSAT,50)) || bm->UserFlags.isSet("upfront-ack", "0"))
        || numberOfReadsLessThan(simplified_solved_InputToSAT,10)
    )
      {
              // If the number of axioms that would be added it small. Remove them.
              bm->UserFlags.ackermannisation = true;
              simplified_solved_InputToSAT = arrayTransformer->TransformFormula_TopLevel(simplified_solved_InputToSAT);
              if (bm->UserFlags.stats_flag)
                cerr << "Have removed array operations" << endl;
              removed = true;
      }

    const bool arrayops = containsArrayOps(simplified_solved_InputToSAT);
    if (removed)
      assert(!arrayops);

    // Run size reducing just once.
    simplified_solved_InputToSAT = sizeReducing(simplified_solved_InputToSAT, bvSolver.get(),pe.get());

    unsigned initial_difficulty_score = difficulty.score(simplified_solved_InputToSAT);

    int bitblasted_difficulty = -1;

    // Fixed point it if it's not too difficult.
    // Currently we discards all the state each time sizeReducing is called,
    // so it's expensive to call.
    if ((!arrayops && initial_difficulty_score < 1000000) || bm->UserFlags.isSet("preserving-fixedpoint", "0"))
           simplified_solved_InputToSAT = callSizeReducing(simplified_solved_InputToSAT, bvSolver.get(),pe.get(), initial_difficulty_score, bitblasted_difficulty);

    if ((!arrayops || bm->UserFlags.isSet("array-difficulty-reversion", "1")))
      {
        initial_difficulty_score = difficulty.score(simplified_solved_InputToSAT);
      }

    if (bitblasted_difficulty != -1 && bm->UserFlags.stats_flag)
      cout << "Initial Bitblasted size:" << bitblasted_difficulty << endl;


    if (bm->UserFlags.stats_flag)
      cout << "Difficulty After Size reducing:" << initial_difficulty_score << endl;

    // So we can delete the object and release all the hash-buckets storage.
    auto_ptr<Revert_to> revert(new Revert_to());

    if ((!arrayops || bm->UserFlags.isSet("array-difficulty-reversion", "1")))
      {
        revert->initialSolverMap.insert(simp->Return_SolverMap()->begin(), simp->Return_SolverMap()->end());
        revert->backup_arrayToIndexToRead.insert(arrayTransformer->arrayToIndexToRead.begin(),arrayTransformer->arrayToIndexToRead.end());
        revert->toRevertTo = simplified_solved_InputToSAT;
      }

    ASTNode inputToSAT;

    //round of substitution, solving, and simplification. ensures that
    //DAG is minimized as much as possibly, and ideally should
    //garuntee that all liketerms in BVPLUSes have been combined.
    bm->SimplifyWrites_InPlace_Flag = false;
    //bm->Begin_RemoveWrites = false;
    //bm->start_abstracting = false;
    bm->TermsAlreadySeenMap_Clear();
    do
      {
        inputToSAT = simplified_solved_InputToSAT;

        if (bm->soft_timeout_expired)
            return SOLVER_TIMEOUT;

        if (bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = pe->topLevel(simplified_solved_InputToSAT, arrayTransformer);

            // Imagine:
            // The simplifier simplifies (0 + T) to T
            // Then bvsolve introduces (0 + T)
            // Then CreateSubstitutionMap decides T maps to a constant, but leaving another (0+T).
            // When we go to simplify (0 + T) will still be in the simplify cache, so will be mapped to T.
            // But it shouldn't be T, it should be a constant.
            // Applying the substitution map fixes this case.
            //
            if (simp->hasUnappliedSubstitutions())
              {
                simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
                simp->haveAppliedSubstitutionMap();
              }

            bm->ASTNodeStats(pe_message.c_str(), simplified_solved_InputToSAT);

            simplified_solved_InputToSAT = simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, false);

            bm->ASTNodeStats(size_inc_message.c_str(), simplified_solved_InputToSAT);
          }

        if (bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats(bitvec_message.c_str(), simplified_solved_InputToSAT);
          }
      }
    while (inputToSAT != simplified_solved_InputToSAT);

    if (bm->UserFlags.bitConstantProp_flag)
      {
        bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
        simplifier::constantBitP::ConstantBitPropagation cb(simp, bm->defaultNodeFactory, simplified_solved_InputToSAT);
        simplified_solved_InputToSAT = cb.topLevelBothWays(simplified_solved_InputToSAT);

        bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

        if (cb.isUnsatisfiable())
          simplified_solved_InputToSAT = bm->ASTFalse;

        bm->ASTNodeStats(cb_message.c_str(), simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.isSet("use-intervals", "1"))
      {
        EstablishIntervals intervals(*bm);
        simplified_solved_InputToSAT = intervals.topLevel_unsignedIntervals(simplified_solved_InputToSAT);
        bm->ASTNodeStats(int_message.c_str(), simplified_solved_InputToSAT);
      }

    // Find pure literals.
    if (bm->UserFlags.isSet("pure-literals", "1"))
      {
        FindPureLiterals fpl;
        bool changed = fpl.topLevel(simplified_solved_InputToSAT, simp, bm);
        if (changed)
          {
            simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
            simp->haveAppliedSubstitutionMap();
            bm->ASTNodeStats(pl_message.c_str(), simplified_solved_InputToSAT);
          }
      }

    if (bm->soft_timeout_expired)
        return SOLVER_TIMEOUT;

    // Simplify using Ite context
    if (bm->UserFlags.optimize_flag && bm->UserFlags.isSet("ite-context", "0"))
      {
        UseITEContext iteC(bm);
        simplified_solved_InputToSAT = iteC.topLevel(simplified_solved_InputToSAT);
        bm->ASTNodeStats("After ITE Context: ", simplified_solved_InputToSAT);
      }

    if (bm->UserFlags.isSet("aig-core-simplify", "0"))
      {
        AIGSimplifyPropositionalCore aigRR(bm);
        simplified_solved_InputToSAT = aigRR.topLevel(simplified_solved_InputToSAT);
        bm->ASTNodeStats("After AIG Core: ", simplified_solved_InputToSAT);
      }

#if 0
    bm->ASTNodeStats("Before SimplifyWrites_Inplace begins: ", simplified_solved_InputToSAT);

    bm->SimplifyWrites_InPlace_Flag = true;
    bm->Begin_RemoveWrites = false;
    bm->start_abstracting = false;
    bm->TermsAlreadySeenMap_Clear();
    do
      {
        inputToSAT = simplified_solved_InputToSAT;

        if (bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = pe->topLevel(simplified_solved_InputToSAT, arrayTransformer);

            if (simp->hasUnappliedSubstitutions())
              {
                simplified_solved_InputToSAT = simp->applySubstitutionMap(simplified_solved_InputToSAT);
                simp->haveAppliedSubstitutionMap();
              }

            bm->ASTNodeStats(pe->message.c_str(), simplified_solved_InputToSAT);

            simplified_solved_InputToSAT = simp->SimplifyFormula_TopLevel(simplified_solved_InputToSAT, false);
            bm->ASTNodeStats("after simplification: ", simplified_solved_InputToSAT);


            if (bm->UserFlags.isSet("always-true", "0"))
              {
                SimplifyingNodeFactory nf(*(bm->hashingNodeFactory), *bm);
                AlwaysTrue always (simp,bm,&nf);
                simplified_solved_InputToSAT = always.topLevel(simplified_solved_InputToSAT);
                bm->ASTNodeStats("After removing always true: ", simplified_solved_InputToSAT);
              }
          }

        // The word level solver uses the simplifier to apply the rewrites it makes,
        // without optimisations enabled. It will enter infinite loops on some input.
        // Instead it could use the apply function of the substitution map, but it
        // doesn't yet...
        if (bm->UserFlags.wordlevel_solve_flag && bm->UserFlags.optimize_flag)
          {
            simplified_solved_InputToSAT = bvSolver->TopLevelBVSolve(simplified_solved_InputToSAT);
            bm->ASTNodeStats("after solving: ", simplified_solved_InputToSAT);
          }
      }
    while (inputToSAT != simplified_solved_InputToSAT);

    bm->ASTNodeStats("After SimplifyWrites_Inplace: ", simplified_solved_InputToSAT);
#endif

    if (bm->UserFlags.isSet("enable-unconstrained", "1"))
      {
        // Remove unconstrained.
        RemoveUnconstrained r(*bm);
        simplified_solved_InputToSAT = r.topLevel(simplified_solved_InputToSAT, simp);
        bm->ASTNodeStats(uc_message.c_str(), simplified_solved_InputToSAT);
      }

    bm->TermsAlreadySeenMap_Clear();

    //bm->start_abstracting = false;
    bm->SimplifyWrites_InPlace_Flag = false;
    //bm->Begin_RemoveWrites = false;

    long final_difficulty_score = difficulty.score(simplified_solved_InputToSAT);

    bool worse= false;
    if (final_difficulty_score > 1.1 * initial_difficulty_score)
        worse = true;

    // It's of course very wasteful to do this! Later I'll make it reuse the work..
    // We bit-blast again, in order to throw it away, so that we can measure whether
    // the number of AIG nodes is smaller. The difficulty score is sometimes completely
    // wrong, the sage-app7 are the motivating examples. The other way to improve it would
    // be to fix the difficulty scorer!
    if (!worse && (bitblasted_difficulty != -1))
     {
        BBNodeManagerAIG bbnm;
        BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&bbnm, simp, bm->defaultNodeFactory , &(bm->UserFlags));
        bb.BBForm(simplified_solved_InputToSAT);
        int newBB=  bbnm.totalNumberOfNodes();
        if (bm->UserFlags.stats_flag)
          cerr << "Final BB Size:" << newBB << endl;

        if (bitblasted_difficulty < newBB)
          worse = true;
    }


    if (bm->UserFlags.stats_flag)
      {
        cerr << "Initial Difficulty Score:" << initial_difficulty_score << endl;
        cerr << "Final Difficulty Score:" << final_difficulty_score << endl;
      }

    bool optimize_enabled = bm->UserFlags.optimize_flag;
    if (worse &&
       (!arrayops || bm->UserFlags.isSet("array-difficulty-reversion", "1")) &&
       bm->UserFlags.isSet("difficulty-reversion", "1"))
      {
        // If the simplified problem is harder, than the
        // initial problem we revert back to the initial
        // problem.

        if (bm->UserFlags.stats_flag)
          cerr << "simplification made the problem harder, reverting." << endl;
        simplified_solved_InputToSAT = revert->toRevertTo;

        // I do this to clear the substitution/solver map.
        // Not sure what would happen if it contained simplifications
        // that haven't been applied.
        simp->ClearAllTables();

        simp->Return_SolverMap()->insert(revert->initialSolverMap.begin(), revert->initialSolverMap.end());
        revert->initialSolverMap.clear();

        // Copy back what we knew about arrays at the start..
        arrayTransformer->arrayToIndexToRead.clear();
        arrayTransformer->arrayToIndexToRead.insert(revert->backup_arrayToIndexToRead.begin(), revert->backup_arrayToIndexToRead.end());

        // The arrayTransformer calls simplify. We don't want
        // it to put back in all the bad simplifications.
        bm->UserFlags.optimize_flag = false;
      }
    revert.reset(NULL);

    simplified_solved_InputToSAT = arrayTransformer->TransformFormula_TopLevel(simplified_solved_InputToSAT);
    bm->ASTNodeStats("after transformation: ", simplified_solved_InputToSAT);
    bm->TermsAlreadySeenMap_Clear();

    bm->UserFlags.optimize_flag = optimize_enabled;

    SOLVER_RETURN_TYPE res;
    if (!bm->UserFlags.ackermannisation)
      {
        bm->counterexample_checking_during_refinement = true;
      }

    // We are about to solve. Clear out all the memory associated with caches
    // that we won't need again.
    simp->ClearCaches();
    simp->haveAppliedSubstitutionMap();
    bm->ClearAllTables();

    // Deleting it clears out all the buckets associated with hashmaps etc. too.
    bvSolver.reset(NULL);
    pe.reset(NULL);


    if (bm->UserFlags.stats_flag)
      simp->printCacheStatus();

    const bool maybeRefinement = arrayops && !bm->UserFlags.ackermannisation;

    simplifier::constantBitP::ConstantBitPropagation* cb = NULL;
    std::auto_ptr<simplifier::constantBitP::ConstantBitPropagation> cleaner;

    if (bm->UserFlags.bitConstantProp_flag)
      {
        bm->GetRunTimes()->start(RunTimes::ConstantBitPropagation);
        cb = new simplifier::constantBitP::ConstantBitPropagation(simp, bm->defaultNodeFactory,
            simplified_solved_InputToSAT);
        cleaner.reset(cb);
        bm->GetRunTimes()->stop(RunTimes::ConstantBitPropagation);

        bm->ASTNodeStats(cb_message.c_str(), simplified_solved_InputToSAT);

        if (cb->isUnsatisfiable())
          simplified_solved_InputToSAT = bm->ASTFalse;
      }

    ToSATAIG toSATAIG(bm, cb, arrayTransformer);

    ToSATBase* satBase = bm->UserFlags.isSet("traditional-cnf", "0") ? tosat : ((ToSAT*) &toSATAIG) ;

    if (bm->soft_timeout_expired)
        return SOLVER_TIMEOUT;

    // If it doesn't contain array operations, use ABC's CNF generation.
    res = Ctr_Example->CallSAT_ResultCheck(NewSolver, simplified_solved_InputToSAT, original_input, satBase,
        maybeRefinement);

    if (bm->soft_timeout_expired)
      {
        if (toSATAIG.cbIsDestructed())
          cleaner.release();

        return SOLVER_TIMEOUT;
      }
    if (SOLVER_UNDECIDED != res)
      {
        // If the aig converter knows that it is never going to be called again,
        // it deletes the constant bit stuff before calling the SAT solver.
        if (toSATAIG.cbIsDestructed())
          cleaner.release();

        CountersAndStats("print_func_stats", bm);
        return res;
      }

    assert(arrayops); // should only go to abstraction refinement if there are array ops.
    assert(!bm->UserFlags.ackermannisation); // Refinement must be enabled too.
    assert (bm->UserFlags.solver_to_use != UserDefinedFlags::MINISAT_PROPAGATORS); // The array solver shouldn't have returned undecided..

    res = Ctr_Example->SATBased_ArrayReadRefinement(NewSolver, simplified_solved_InputToSAT, original_input, satBase);
    if (SOLVER_UNDECIDED != res)
      {
        if (toSATAIG.cbIsDestructed())
          cleaner.release();

        CountersAndStats("print_func_stats", bm);
        return res;
      }

    #if 0
    res = Ctr_Example->SATBased_ArrayWriteRefinement(NewSolver, original_input, satBase);
    if (SOLVER_UNDECIDED != res)
      {
        if (toSATAIG.cbIsDestructed())
          cleaner.release();

        CountersAndStats("print_func_stats", bm);
        return res;
      }

    res = Ctr_Example->SATBased_ArrayReadRefinement(NewSolver, simplified_solved_InputToSAT, original_input, satBase);
    if (SOLVER_UNDECIDED != res)
      {
        if (toSATAIG.cbIsDestructed())
          cleaner.release();

        CountersAndStats("print_func_stats", bm);
        return res;
      }
    #endif

    FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
      "either a divide by zero in the input or a bug in STP");
    //bogus return to make the compiler shut up
    return SOLVER_ERROR;


  } //End of TopLevelSTPAux

#if 0

  //UserGuided abstraction refinement
  SOLVER_RETURN_TYPE
  STP::
  UserGuided_AbsRefine(SATSolver& NewSolver,
		       const ASTNode& original_input)
  {
    ASTVec v = bm->GetAsserts_WithKey(0);
    if(v.empty())
      {
	FatalError("UserGuided_AbsRefine: Something is seriously wrong."\
		   "The input set is empty");
      }
    ASTNode sureAddInput = 
      (v.size() == 1) ? v[0] : bm->CreateNode(AND, v); 

    SOLVER_RETURN_TYPE res = SOLVER_UNDECIDED;
    res = TopLevelSTPAux(NewSolver, sureAddInput, original_input);
    if(SOLVER_UNDECIDED != res)
      {
	return res;
      }
    
    //Do refinement here
    if(AND != original_input.GetKind())
      {
	FatalError("UserGuided_AbsRefine: The input must be an AND");
      }

    ASTVec RefineFormulasVec;
    ASTVec RemainingFormulasVec;
    ASTNode asttrue = bm->CreateNode(TRUE);
    ASTNode astfalse = bm->CreateNode(FALSE);
    for(int count=0; count < bm->UserFlags.num_absrefine; count++)
      {
	RemainingFormulasVec.clear();
	RemainingFormulasVec.push_back(asttrue);
	RefineFormulasVec.clear();	
	RefineFormulasVec.push_back(asttrue);
	ASTVec InputKids = original_input.GetChildren();
	for(ASTVec::iterator it = InputKids.begin(), itend = InputKids.end();
	    it!=itend;it++)
	  {
	    Ctr_Example->ClearComputeFormulaMap();
	    if(astfalse == Ctr_Example->ComputeFormulaUsingModel(*it))
	      {
		RefineFormulasVec.push_back(*it);
	      }
	    else
	      {
		RemainingFormulasVec.push_back(*it);
	      }
	  }
	ASTNode RefineFormulas =
	  (RefineFormulasVec.size() == 1) ?
	  RefineFormulasVec[0] : bm->CreateNode(AND, RefineFormulasVec);
	res = TopLevelSTPAux(NewSolver, RefineFormulas, original_input);
	if(SOLVER_UNDECIDED != res)
	  {
	    return res;
	  }
      }

    ASTNode RemainingFormulas = 
      (RemainingFormulasVec.size() == 1) ?
      RemainingFormulasVec[0] : bm->CreateNode(AND, RemainingFormulasVec);
    res = TopLevelSTPAux(NewSolver, RemainingFormulas, original_input);
    
    if(SOLVER_UNDECIDED != res)
      {
	return res;
      }
    
    FatalError("TopLevelSTPAux: reached the end without proper conclusion:"
	       "either a divide by zero in the input or a bug in STP");    
    return SOLVER_ERROR;
  } //End of UserGuided_AbsRefine()
#endif

}; //end of namespace
