// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include <assert.h>
#include <math.h>
#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "AbsRefine_CounterExample.h"

namespace BEEV
{
  /******************************************************************
   * Abstraction Refinement related functions
   ******************************************************************/  

    enum Polarity
    {
        LEFT_ONLY, RIGHT_ONLY, BOTH
    };

    void
    getSatVariables(const ASTNode & a, vector<unsigned> & v_a, SATSolver & SatSolver,
            ToSATBase::ASTNodeToSATVar & satVar)
    {
        ToSATBase::ASTNodeToSATVar::iterator it = satVar.find(a);
        if (it != satVar.end())
            v_a = it->second;
        else if (!a.isConstant())
            {
                assert(a.GetKind() == SYMBOL);
                // It was ommitted from the initial problem, so assign it freshly.
                for (int i = 0; i < a.GetValueWidth(); i++)
                    {
                        SATSolver::Var v = SatSolver.newVar();
                        // We probably don't want the variable eliminated.
                        SatSolver.setFrozen(v);
                        v_a.push_back(v);
                    }
                satVar.insert(make_pair(a, v_a));
            }
    }


    // This function adds the clauses to constrain that "a" and "b" equal a fresh variable
    // (which it returns).
    // Because it's used to create array axionms (a=b)-> (c=d), it can be
    // used to only add one of the two polarities.
    Minisat::Var
    getEquals(SATSolver& SatSolver, const ASTNode& a, const ASTNode& b, ToSATBase::ASTNodeToSATVar& satVar,
            Polarity polary = BOTH)
    {
        const int width = a.GetValueWidth();
        assert(width == b.GetValueWidth());
        assert(!a.isConstant() || !b.isConstant());

        vector<unsigned> v_a;
        vector<unsigned> v_b;

        getSatVariables(a, v_a, SatSolver, satVar);
        getSatVariables(b, v_b, SatSolver, satVar);

        // The only time v_a or v_b will be empty is if "a" resp. "b" is a constant.

        if (v_a.size() == width && v_b.size() == width)
            {
                SATSolver::vec_literals all;
                const int result = SatSolver.newVar();

                for (int i = 0; i < width; i++)
                    {
                        SATSolver::vec_literals s;

                        if (polary != RIGHT_ONLY)
                            {
                                int nv0 = SatSolver.newVar();
                                s.push(SATSolver::mkLit(v_a[i], true));
                                s.push(SATSolver::mkLit(v_b[i], true));
                                s.push(SATSolver::mkLit(nv0, false));
                                SatSolver.addClause(s);
                                s.clear();

                                s.push(SATSolver::mkLit(v_a[i], false));
                                s.push(SATSolver::mkLit(v_b[i], false));
                                s.push(SATSolver::mkLit(nv0, false));
                                SatSolver.addClause(s);
                                s.clear();

                                all.push(SATSolver::mkLit(nv0, true));
                            }

                        if (polary != LEFT_ONLY)
                            {
                                s.push(SATSolver::mkLit(v_a[i], true));
                                s.push(SATSolver::mkLit(v_b[i], false));
                                s.push(SATSolver::mkLit(result, true));
                                SatSolver.addClause(s);
                                s.clear();

                                s.push(SATSolver::mkLit(v_a[i], false));
                                s.push(SATSolver::mkLit(v_b[i], true));
                                s.push(SATSolver::mkLit(result, true));
                                SatSolver.addClause(s);
                                s.clear();
                            }
                    }
                if (all.size() > 0)
                {
                        all.push(SATSolver::mkLit(result, false));
                        SatSolver.addClause(all);
                }
                return result;
            }
        else if (v_a.size() == 0 ^ v_b.size() == 0)
            {
                ASTNode constant = a.isConstant() ? a : b;
                vector<unsigned> vec = v_a.size() == 0 ? v_b : v_a;
                assert(constant.isConstant());
                assert(vec.size() == width);

                SATSolver::vec_literals all;
                const int result = SatSolver.newVar();
                all.push(SATSolver::mkLit(result, false));

                CBV v = constant.GetBVConst();
                for (int i = 0; i < width; i++)
                    {
                        if (polary != RIGHT_ONLY)
                            {
                                if (CONSTANTBV::BitVector_bit_test(v, i))
                                    all.push(SATSolver::mkLit(vec[i], true));
                                else
                                    all.push(SATSolver::mkLit(vec[i], false));
                            }

                        if (polary != LEFT_ONLY)
                            {
                                SATSolver::vec_literals p;
                                p.push(SATSolver::mkLit(result, true));
                                if (CONSTANTBV::BitVector_bit_test(v, i))
                                    p.push(SATSolver::mkLit(vec[i], false));
                                else
                                    p.push(SATSolver::mkLit(vec[i], true));

                                SatSolver.addClause(p);
                            }

                    }
                if (all.size() > 1)
                    SatSolver.addClause(all);
                return result;
            }
        else
            FatalError("Unexpected, both must be constants..");
    }


  /******************************************************************
   * ARRAY READ ABSTRACTION REFINEMENT
   *   
   * SATBased_ArrayReadRefinement()
   *
   * What it really does is, for each array, loop over each index i.
   * inside that loop, it finds all the true and false axioms with i
   * as first index.  When it's got them all, it adds the false axioms
   * to the formula and re-solves, and returns if the result is
   * correct.  Otherwise, it goes on to the next index.
   *
   * If it gets through all the indices without a correct result
   * (which I think is impossible), it then solves with all the true
   * axioms, too.
   *
   * This is not the most obvious way to do it, and I don't know how
   * it compares with other approaches (e.g., one false axiom at a
   * time or all the false axioms each time).
   *****************************************************************/
  struct AxiomToBe
    {
        AxiomToBe(ASTNode i0, ASTNode i1, ASTNode v0, ASTNode v1)
        {
            index0 = i0;
            index1 = i1;
            value0 = v0;
            value1 = v1;
        }
        ASTNode index0, index1;
        ASTNode value0, value1;

        int
        numberOfConstants() const
        {
            return ((index0.isConstant() ? 1 : 0) + (index1.isConstant() ? 1 : 0) + (index0.isConstant() ? 1 : 0)
                    + (index1.isConstant() ? 1 : 0));
        }

    };

  void
    applyAxiomToSAT(SATSolver & SatSolver, AxiomToBe& toBe, ToSATBase::ASTNodeToSATVar & satVar)
    {
        Minisat::Var a = getEquals(SatSolver, toBe.index0, toBe.index1, satVar, LEFT_ONLY);
        Minisat::Var b = getEquals(SatSolver, toBe.value0, toBe.value1, satVar, RIGHT_ONLY);
        SATSolver::vec_literals satSolverClause;
        satSolverClause.push(SATSolver::mkLit(a, true));
        satSolverClause.push(SATSolver::mkLit(b, false));
        SatSolver.addClause(satSolverClause);
    }

    void
    applyAxiomsToSolver(ToSATBase::ASTNodeToSATVar & satVar, vector<AxiomToBe> & toBe, SATSolver & SatSolver)
    {
        for (int i = 0; i < toBe.size(); i++)
            {
                applyAxiomToSAT(SatSolver, toBe[i], satVar);
            }
        toBe.clear();
    }

    bool
    sortBySize(const pair<ASTNode, ArrayTransformer::arrTypeMap>& a,
            const pair<ASTNode, ArrayTransformer::arrTypeMap>& b)
    {
        return a.second.size() < b.second.size();
    }

    bool
    sortByIndexConstants(const pair<ASTNode, ArrayTransformer::ArrayRead> & a,
            const pair<ASTNode, ArrayTransformer::ArrayRead> & b)
    {
        int aCount = ((a.second.index_symbol.isConstant()) ? 2 : 0) + (a.second.symbol.isConstant() ? 1 : 0);
        int bCount = ((b.second.index_symbol.isConstant()) ? 2 : 0) + (b.second.symbol.isConstant() ? 1 : 0);
        return aCount > bCount;
    }

    bool
    sortbyConstants(const AxiomToBe & a, const AxiomToBe & b)
    {
        return a.numberOfConstants() > b.numberOfConstants();
    }

    SOLVER_RETURN_TYPE
    AbsRefine_CounterExample::SATBased_ArrayReadRefinement(SATSolver & SatSolver, const ASTNode & inputAlreadyInSAT,
            const ASTNode & original_input, ToSATBase *tosat)
    {
        vector<AxiomToBe> RemainingAxiomsVec;
        vector<AxiomToBe> FalseAxiomsVec;
        // NB. Because we stop this timer before entering the SAT solver, the count
        // it produces isn't the number of times Array Read Refinement was entered.
        bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
        /// Check the arrays with the least indexes first.


        vector<pair<ASTNode, ArrayTransformer::arrTypeMap> > arrayToIndex;
        arrayToIndex.insert(arrayToIndex.begin(), ArrayTransform->arrayToIndexToRead.begin(),
                ArrayTransform->arrayToIndexToRead.end());
        sort(arrayToIndex.begin(), arrayToIndex.end(), sortBySize);

        //In these loops we try to construct Leibnitz axioms and add it to
        //the solve(). We add only those axioms that are false in the
        //current counterexample. we keep adding the axioms until there
        //are no more axioms to add
        //
        //for each array, fetch its list of indices seen so far
        for (vector<pair<ASTNode, ArrayTransformer::arrTypeMap> >::const_iterator iset = arrayToIndex.begin(),
                iset_end = arrayToIndex.end(); iset != iset_end; iset++)
            {
                const ASTNode& ArrName = iset->first;
                const map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

                vector<ASTNode> listOfIndices;
                listOfIndices.reserve(mapper.size());

                // Make a vector of the read symbols.
                ASTVec read_node_symbols;
                read_node_symbols.reserve(listOfIndices.size());

                vector<Kind> jKind;
                jKind.reserve(mapper.size());

                vector<ASTNode> concreteIndexes;
                concreteIndexes.reserve(mapper.size());

                vector<ASTNode> concreteValues;
                concreteValues.reserve(mapper.size());

                ASTVec index_symbols;

                vector<pair<ASTNode, ArrayTransformer::ArrayRead> > indexToRead;
                indexToRead.insert(indexToRead.begin(), mapper.begin(), mapper.end());
                sort(indexToRead.begin(), indexToRead.end(), sortByIndexConstants);

                for (vector<pair<ASTNode, ArrayTransformer::ArrayRead> >::const_iterator it = indexToRead.begin(); it
                        != indexToRead.end(); it++)
                    {
                        const ASTNode& the_index = it->first;
                        listOfIndices.push_back(the_index);

                        ASTNode arrsym = it->second.symbol;
                        read_node_symbols.push_back(arrsym);

                        index_symbols.push_back(it->second.index_symbol);

                        assert(read_node_symbols[0].GetValueWidth() == arrsym.GetValueWidth());
                        assert(listOfIndices[0].GetValueWidth() == the_index.GetValueWidth());

                        jKind.push_back(the_index.GetKind());

                        concreteIndexes.push_back(TermToConstTermUsingModel(the_index));
                        concreteValues.push_back(TermToConstTermUsingModel(arrsym));
                    }

                assert(listOfIndices.size() == mapper.size());

                //loop over the list of indices for the array and create LA,
                //and add to inputAlreadyInSAT
                for (int i = 0; i < listOfIndices.size(); i++)
                    {
                        const ASTNode& index_i = listOfIndices[i];
                        const Kind iKind = index_i.GetKind();

                        // Create all distinct pairs of indexes.
                        for (int j = i + 1; j < listOfIndices.size(); j++)
                            {
                                const ASTNode& index_j = listOfIndices[j];

                                // If the index is a constant, and different, then there's no reason to check.
                                // Sometimes we get the same index stored multiple times in the array. Not sure why...
                                if (BVCONST == iKind && jKind[j] == BVCONST && index_i != index_j)
                                    continue;

                                if (ASTFalse == simp->CreateSimplifiedEQ(index_i, index_j))
                                    continue; // shortcut.

                                AxiomToBe o(index_symbols[i], index_symbols[j], read_node_symbols[i],
                                        read_node_symbols[j]);

                                if (concreteIndexes[i] == concreteIndexes[j] && concreteValues[i] != concreteValues[j])
                                    {
                                        FalseAxiomsVec.push_back(o);
                                        //ToSATBase::ASTNodeToSATVar	& satVar = tosat->SATVar_to_SymbolIndexMap();
                                        //applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);
                                    }
                                else
                                    RemainingAxiomsVec.push_back(o);
                            }
                        if (FalseAxiomsVec.size() > 0)
                            {
                                ToSATBase::ASTNodeToSATVar & satVar = tosat->SATVar_to_SymbolIndexMap();
                                applyAxiomsToSolver(satVar, FalseAxiomsVec, SatSolver);

                                SOLVER_RETURN_TYPE res2;
                                bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
                                res2 = CallSAT_ResultCheck(SatSolver, ASTTrue, original_input, tosat, true);

                                if (SOLVER_UNDECIDED != res2)
                                    return res2;
                                bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
                            }
                    }
            }
#if 1
        if (RemainingAxiomsVec.size() > 0)
            {
                if (bm->UserFlags.stats_flag)
                {
                        cout << "Adding all the remaining " << RemainingAxiomsVec.size() << " read axioms " << endl;
                }
                ToSATBase::ASTNodeToSATVar & satVar = tosat->SATVar_to_SymbolIndexMap();
                applyAxiomsToSolver(satVar, RemainingAxiomsVec, SatSolver);

                bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
                return CallSAT_ResultCheck(SatSolver, ASTTrue, original_input, tosat, true);
            }
       // For difficult problems, I suspec this is a better way to do it.
       // However because it can cause an extra three SAT solver calls, it slows down
       // easy problems.
#else
        if(RemainingAxiomsVec.size() > 0)
            {
                // Add the axioms in order of how many constants there are in each.

                ToSATBase::ASTNodeToSATVar & satVar = tosat->SATVar_to_SymbolIndexMap();
                sort(RemainingAxiomsVec.begin(), RemainingAxiomsVec.end(), sortbyConstants);
                int current_position = 0;
                for(int n_const = 4;n_const >= 0;n_const--)
                    {
                        bool added =false;
                        while(current_position < RemainingAxiomsVec.size() && RemainingAxiomsVec[current_position].numberOfConstants() == n_const)
                            {
                                AxiomToBe & toBe = RemainingAxiomsVec[current_position];
                                applyAxiomToSAT(SatSolver, toBe,satVar);
                                current_position++;
                                added = true;
                            }
                        if (!added)
                            continue;
                        bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
                        SOLVER_RETURN_TYPE res2;
                        res2 = CallSAT_ResultCheck(SatSolver, ASTTrue, original_input, tosat, true);
                        if(SOLVER_UNDECIDED != res2)
                        return res2;

                        bm->GetRunTimes()->start(RunTimes::ArrayReadRefinement);
                    }
                assert(current_position == RemainingAxiomsVec.size());
                RemainingAxiomsVec.clear();
                assert(SOLVER_UNDECIDED == CallSAT_ResultCheck(SatSolver, ASTTrue, original_input, tosat, true));
            }
#endif

        bm->GetRunTimes()->stop(RunTimes::ArrayReadRefinement);
        return SOLVER_UNDECIDED;
    } //end of SATBased_ArrayReadRefinement


#if 0
    // This isn't currently wired up.

  /******************************************************************
   * ARRAY WRITE ABSTRACTION REFINEMENT
   *
   * FIXME: Write Detailed Comment
   *****************************************************************/
  SOLVER_RETURN_TYPE 
  AbsRefine_CounterExample::
  SATBased_ArrayWriteRefinement(SATSolver& SatSolver,
                                const ASTNode& original_input,
                                ToSATBase *tosat
                              )
  {
    ASTNode writeAxiom;
    ASTNodeMap::const_iterator it = simp->ReadOverWriteMap()->begin();
    ASTNodeMap::const_iterator itend = simp->ReadOverWriteMap()->end();

    ASTVec FalseAxioms, RemainingAxioms;
    RemainingAxioms.push_back(ASTTrue);
    for (; it != itend; it++)
      {
        //Guided refinement starts here
        ClearComputeFormulaMap();
        writeAxiom = Create_ArrayWriteAxioms(it->first, it->second);
        if (ASTFalse == ComputeFormulaUsingModel(writeAxiom))
          {
            writeAxiom = ArrayTransform->TransformFormula_TopLevel(writeAxiom);
            FalseAxioms.push_back(writeAxiom);
          }
        else
          {
            writeAxiom = ArrayTransform->TransformFormula_TopLevel(writeAxiom);
            RemainingAxioms.push_back(writeAxiom);
          }
      }

    SOLVER_RETURN_TYPE res2 = SOLVER_UNDECIDED;
    if (FalseAxioms.size() > 0)
    {
		writeAxiom = (FalseAxioms.size() != 1) ? bm->CreateNode(AND,
				FalseAxioms) : FalseAxioms[0];
		bm->ASTNodeStats("adding false writeaxiom to SAT: ", writeAxiom);
		res2 = CallSAT_ResultCheck(SatSolver, writeAxiom, original_input, tosat,true);
	}

    if (SOLVER_UNDECIDED != res2)
      {
        return res2;
      }

    if (RemainingAxioms.size() > 0)
    {
		writeAxiom =
		  (RemainingAxioms.size() != 1) ?
		  bm->CreateNode(AND, RemainingAxioms) : RemainingAxioms[0];
		bm->ASTNodeStats("adding remaining writeaxiom to SAT: ", writeAxiom);
		res2 = CallSAT_ResultCheck(SatSolver,
								   writeAxiom,
								   original_input,
								   tosat, true);
    }
    return res2;
  } //end of SATBased_ArrayWriteRefinement
  
  //Creates Array Write Axioms
  ASTNode 
  AbsRefine_CounterExample::Create_ArrayWriteAxioms(const ASTNode& term, 
                                                    const ASTNode& newvar)
  {
    if (READ != term.GetKind() && WRITE != term[0].GetKind())
      {
        FatalError("Create_ArrayWriteAxioms: "\
                   "Input must be a READ over a WRITE", term);
      }

    ASTNode lhs = newvar;
    ASTNode rhs = term;
    ASTNode arraywrite_axiom = simp->CreateSimplifiedEQ(lhs, rhs);
    return arraywrite_axiom;
  }//end of Create_ArrayWriteAxioms()
#endif
};// end of namespace BEEV
