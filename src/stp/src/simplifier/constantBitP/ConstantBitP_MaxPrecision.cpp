#include "ConstantBitP_MaxPrecision.h"
#include "../../AST/AST.h"
#include "../../AST/ArrayTransformer.h"
#include "../../simplifier/simplifier.h"
#include "../../to-sat/BitBlaster.h"
#include "../../to-sat/AIG/BBNodeManagerAIG.h"
#include "../../absrefine_counterexample/AbsRefine_CounterExample.h"
#include "../../to-sat/ASTNode/ToSAT.h"
#include "../../to-sat/AIG/ToSATAIG.h"
#include "../../STPManager/STPManager.h"
#include "../../sat/MinisatCore.h"

using namespace BEEV;

namespace simplifier
{

namespace constantBitP
{

void print(const vector<FixedBits*> children, const FixedBits& output, Kind k);

//// Help node creation functions.

ASTNode createConstant(int bitWidth, int val, STPMgr* beev)
{
	CBV cbv = CONSTANTBV::BitVector_Create(bitWidth, true);
	int max = bitWidth > ((int) sizeof(int) * 8) ? sizeof(int) * 8 : bitWidth;
	for (int i = 0; i < max; i++)
		if (val & (1 << i))
			CONSTANTBV::BitVector_Bit_On(cbv, i);
	return beev->CreateBVConst(cbv, bitWidth);
}

ASTNode createTerm(Kind k, int width, const ASTNode& n1, STPMgr* beev)
{
	ASTNode result = beev->CreateTerm(k, width, n1);
	BVTypeCheck(result);
	return result;
}

ASTNode createTerm(Kind k, int width, const ASTNode& n1, const ASTNode& n2, STPMgr* beev)
{
	ASTNode result = beev->CreateTerm(k, width, n1, n2);
	BVTypeCheck(result);
	return result;
}

ASTNode createNode(Kind k, const ASTNode& n1, const ASTNode& n2, STPMgr* beev)
{
	ASTNode result = beev->CreateNode(k, n1, n2);
	BVTypeCheck(result);
	return result;
}

ASTNode createTerm(Kind k, int width, const ASTNode& n1, const ASTNode& n2, const ASTNode& n3, STPMgr* beev)
{
	ASTNode result = beev->CreateTerm(k, width, n1, n2, n3);
	BVTypeCheck(result);
	return result;
}

//////////////////////////////////////////////////

// Concretisation function. Gamma.
void concretise(const ASTNode& variable, const FixedBits& fixed, ASTVec& list, STPMgr* beev)
{
	if (BOOLEAN_TYPE == variable.GetType())
	{
		assert(1 == fixed.getWidth());
		assert(fixed.isBoolean());

		if (fixed.isFixed(0))
		{
			ASTNode assert;
			if (!fixed.getValue(0)) // if it's false, try to find a true assignment.
				assert = variable;
			else
				assert = beev->CreateNode(NOT, variable);
			list.push_back(assert);
		}
	}
	else
	{
		assert(BITVECTOR_TYPE == variable.GetType());
		assert(variable.GetValueWidth() == (unsigned)fixed.getWidth());
		for (int i = 0; i < fixed.getWidth(); i++)
		{
			if (fixed.isFixed(i))
			{
				ASTNode oneOrZero = createConstant(1, fixed.getValue(i) ? 0 : -1, beev); // NB: swapped.
				ASTNode location = createConstant(32, i, beev);
				ASTNode extract = createTerm(BVEXTRACT, 1, variable, location, location, beev);
				ASTNode assert = createNode(EQ, extract, oneOrZero, beev);
				list.push_back(assert);
			}
		}
	}
}


// Concretisation function. Gamma.
void concretise(const ASTNode& variable, const FixedBits& fixed, SATSolver::vec_literals& satSolverClause, STPMgr* beev, ToSATBase::ASTNodeToSATVar& map)
{
        if (BOOLEAN_TYPE == variable.GetType())
        {
                assert(1 == fixed.getWidth());
                assert(fixed.isBoolean());

                if (fixed.isFixed(0))
                {
                        if (!fixed.getValue(0)) // if it's false, try to find a true assignment.
                          {
                            assert(map.find(variable) != map.end());
                            int v = (map.find(variable)->second)[0];
                            satSolverClause.push(SATSolver::mkLit(v, false));
                          }
                        else
                          {
                            assert(map.find(variable) != map.end());
                            int v = (map.find(variable)->second)[0];
                            satSolverClause.push(SATSolver::mkLit(v, true));
                          }

                }
        }
        else
        {
                assert(BITVECTOR_TYPE == variable.GetType());
                assert(variable.GetValueWidth() == (unsigned)fixed.getWidth());
                for (int i = 0; i < fixed.getWidth(); i++)
                {
                        if (fixed.isFixed(i))
                        {
                            assert(map.find(variable) != map.end());
                            int v = (map.find(variable)->second)[i];
                            satSolverClause.push(SATSolver::mkLit(v, fixed.getValue(i)));
                        }
                }
        }
}


// Concretisation function. Gamma.
void concretiseB(const ASTNode& variable, const ASTNode& min, const ASTNode& max, ASTVec& list, STPMgr* beev)
{
    assert(min.isConstant());
    assert(max.isConstant());

        if (BOOLEAN_TYPE == variable.GetType())
        {
            assert(false); // not yet implemented.
        }
        else
        {
                assert(BITVECTOR_TYPE == variable.GetType());
                ASTNode assert = createNode(BVLT, variable, min, beev);
                list.push_back(assert);

                assert = createNode(BVGT, variable, max, beev);
                list.push_back(assert);
        }
}




bool fix(FixedBits& a, const FixedBits& b, const int i);


Result fix(FixedBits& b, BEEV::CBV low, BEEV::CBV high);



// The bitWidth isn't necessarily the same for all children. e.g. ITE(boolean, x-bit, x-bit)
bool maxBoundsPrecision(vector<FixedBits*> children, FixedBits& output, Kind kind, STPMgr* beev)
{
        const int numberOfChildren = children.size();

        bool disabledProp = !beev->UserFlags.bitConstantProp_flag;
        bool printOutput = beev->UserFlags.print_output_flag;

        beev->UserFlags.bitConstantProp_flag = false;
        beev->UserFlags.print_output_flag = false;

        ASTVec initialFixing;

        //Create a variable to represent each input, and one for the output.
        ASTVec variables;
        for (int i = 0; i < numberOfChildren; i++)
        {
          std::stringstream out;
          out << "v" << i;

          unsigned valueWidth;

          if (children[i]->isBoolean())
              valueWidth = 0;
           else
              valueWidth = (children[i]->getWidth());

          ASTNode node = beev->CreateSymbol(out.str().c_str(), 0, valueWidth);
          variables.push_back(node);

          // constrain the fixed bits of each input variable not to change.
          concretise(node, *children[i], initialFixing, beev);
        }

        unsigned outputWidth = output.isBoolean()? 0: output.getWidth();
        ASTNode outputNode = beev->CreateSymbol("result",0,outputWidth);

        ASTNode expr;
        if (output.isBoolean())
        {
                ASTNode p1 = beev->CreateNode(kind, variables);
                BVTypeCheck(p1);
                expr = createNode(IFF, p1, outputNode, beev);
        }
        else
        {
                ASTNode p1 = beev->CreateTerm(kind, output.getWidth(), variables);
                BVTypeCheck(p1);
                expr = createNode(EQ, p1, outputNode, beev);
        }

        // constrain the input to equal the output.
        BVTypeCheck(expr);

        // constrain the fixed parts of the output node not to change.
        concretise(outputNode, output, initialFixing, beev);

        ASTVec notted;
        for (ASTVec::const_iterator i = initialFixing.begin(); i != initialFixing.end(); i++)
                notted.push_back(beev->CreateNode(NOT, *i));

        if (notted.size() > 0) // some are specified.
        {
                expr = beev->CreateNode(BEEV::AND, expr, beev->CreateNode(BEEV::AND, notted));
        }

        bool first = true;
        ASTVec ors;
        ASTNode total = beev->ASTTrue;
        Simplifier simp(beev);
        ArrayTransformer at(beev,&simp);
        AbsRefine_CounterExample ce(beev,&simp,&at);
        ToSAT tosat(beev);
        bool timeout = false;
        MinisatCore<Minisat::Solver> newS(timeout);

        vector<ASTNode> min_children(children.size());
        vector<ASTNode> max_children(children.size());
        ASTNode min_output;
        ASTNode max_output;


        while (true)
        {
                ASTNode toSolve;

                if (first)
                {
                        toSolve = expr;
                }
                else
                {
                        assert(ors.size() !=0);
                        if (ors.size() > 1)
                                toSolve = beev->CreateNode(BEEV::OR, ors);
                        else
                                toSolve = ors[0];
                        ors.clear();
                }

                BVTypeCheck(toSolve);

                // Some operations aren't bitblasted directly. For example sbvmod is converted into
                // other operations first.
                //ArrayTransformer(STPMgr * bm, Simplifier* s, NodeFactory &nodeFactory_) :

                toSolve = at.TransformFormula_TopLevel(toSolve);
                total= beev->CreateNode(AND, total, toSolve);
                int result = ce.CallSAT_ResultCheck(newS, total, total, &tosat,true);

                if (2 == result)
                        FatalError("error from solver");
                else if (1 == result)
                {
                        break; // UNSAT use the last one..
                }

                if (first)
                {
                        // Don't do the meet the first time through. Set the input and output.

                        for (int i = 0; i < numberOfChildren; i++)
                        {
                                ASTNode n = (ce.GetCounterExample(true, variables[i]));
                                min_children[i]  = n;
                                max_children[i]  = n;
                                concretiseB(variables[i], n,n, ors, beev);
                        }

                        ASTNode n = (ce.GetCounterExample(true, outputNode));
                        min_output = n;
                        max_output = n;
                        concretiseB(outputNode,n,n, ors, beev);
                }
                else
                {
                        for (int i = 0; i < numberOfChildren; i++)
                        {
                                ASTNode n = (ce.GetCounterExample(true, variables[i]));
                                //cerr << variables[i].GetName() << " " << n << endl;
                                ASTNode t = beev->CreateNode(BVLT, n, min_children[i]);
                                if (beev->ASTTrue == NonMemberBVConstEvaluator(t))
                                    min_children[i] = n;
                                t = beev->CreateNode(BVGT, n, max_children[i]);
                                if (beev->ASTTrue == NonMemberBVConstEvaluator(t))
                                    max_children[i] = n;
                                concretiseB(variables[i], min_children[i], max_children[i], ors, beev);
                        }


                        ASTNode n = (ce.GetCounterExample(true, outputNode));
                        //cerr << variables[i].GetName() << " " << n << endl;
                        ASTNode t = beev->CreateNode(BVLT, n, min_output);
                        if (beev->ASTTrue == NonMemberBVConstEvaluator(t))
                            min_output = n;
                        t = beev->CreateNode(BVGT, n, max_output);
                        if (beev->ASTTrue == NonMemberBVConstEvaluator(t))
                            max_output = n;
                        concretiseB(outputNode, min_output, max_output, ors, beev);
                }

                first = false;

                //print(children, output, kind);

                if (0 == ors.size())
                        break; // everything is at top.

                //beev->AddAssert(beev->CreateNode(BEEV::OR, ors));
        }

        if (!first)
          {
        for (int i = 0; i < numberOfChildren; i++)
        {
             simplifier::constantBitP::fix(*children[i], min_children[i].GetBVConst(), max_children[i].GetBVConst());
         }

        simplifier::constantBitP::fix(output, min_output.GetBVConst(), max_output.GetBVConst());
          }


        //beev->ClearSATTables();
        //beev->ClearAllCaches();

        // The first time we AddAsserts() it creates a new ASTVec to store them (on the heap).
        beev->Pop();

        beev->UserFlags.bitConstantProp_flag = !disabledProp;
        beev->UserFlags.print_output_flag = printOutput;

        return first;
}

// The bitWidth isn't necessarily the same for all children. e.g. ITE(boolean, x-bit, x-bit)
bool maxPrecision(vector<FixedBits*> children, FixedBits& output, Kind kind, STPMgr* beev)
{
	const int numberOfChildren = children.size();

	bool disabledProp = !beev->UserFlags.bitConstantProp_flag;
	bool printOutput = beev->UserFlags.print_output_flag;
	bool checkCounter = beev->UserFlags.check_counterexample_flag;

	beev->UserFlags.bitConstantProp_flag = false;
	beev->UserFlags.print_output_flag = false;
	beev->UserFlags.check_counterexample_flag= false;

	ASTVec initialFixing;

	//Create a variable to represent each input, and one for the output.
	ASTVec variables;
	for (int i = 0; i < numberOfChildren; i++)
        {
          std::stringstream out;
          out << "v_VERY_SPECIALLY_NAMES" << i;

          unsigned valueWidth;

          if (children[i]->isBoolean())
              valueWidth = 0;
           else
              valueWidth = (children[i]->getWidth());

          ASTNode node = beev->CreateSymbol(out.str().c_str(), 0, valueWidth);
          variables.push_back(node);

          // constrain the fixed bits of each input variable not to change.
          concretise(node, *children[i], initialFixing, beev);
        }

	unsigned outputWidth = output.isBoolean()? 0: output.getWidth();
	ASTNode outputNode = beev->CreateSymbol("result_WITH_SPECIAL_NAME",0,outputWidth);

	ASTNode expr;
	if (output.isBoolean())
	{
		ASTNode p1 = beev->CreateNode(kind, variables);
		BVTypeCheck(p1);
		expr = createNode(IFF, p1, outputNode, beev);
	}
	else
	{
		ASTNode p1 = beev->CreateTerm(kind, output.getWidth(), variables);
		BVTypeCheck(p1);
		expr = createNode(EQ, p1, outputNode, beev);
	}

	// constrain the input to equal the output.
	BVTypeCheck(expr);

	// constrain the fixed parts of the output node not to change.
	concretise(outputNode, output, initialFixing, beev);

	ASTVec notted;
	for (ASTVec::const_iterator i = initialFixing.begin(); i != initialFixing.end(); i++)
		notted.push_back(beev->CreateNode(NOT, *i));

	if (notted.size() > 0) // some are specified.
	{
		expr = beev->CreateNode(BEEV::AND, expr, beev->CreateNode(BEEV::AND, notted));
	}


	bool first = true;
        Simplifier simp(beev);
        ArrayTransformer at(beev,&simp);
        AbsRefine_CounterExample ce(beev,&simp,&at);
        bool timeout = false;
        MinisatCore<Minisat::Solver> newS(timeout);

        ToSATAIG tosat(beev,&at);

        SATSolver::vec_literals satSolverClause;

	while (true)
	{

	      int result;

		if (first)
		{
		  beev->AddQuery(beev->ASTUndefined);
		  result = ce.CallSAT_ResultCheck(newS, expr, expr, &tosat,true);
		}
		else
		{
		    assert(satSolverClause.size() > 0);
		    newS.addClause(satSolverClause);
		    satSolverClause.clear();

		    beev->AddQuery(beev->ASTUndefined);
		    result = ce.CallSAT_ResultCheck(newS, beev->ASTTrue, beev->ASTTrue, &tosat,true);
		}

		if (2 == result)
			FatalError("error from solver");
		else if (1 == result)
		{
			break; // UNSAT use the last one..
		}

		if (first)
		{
			// Don't do the meet the first time through. Set the input and output.

			for (int i = 0; i < numberOfChildren; i++)
			{
				ASTNode n = (ce.GetCounterExample(true, variables[i]));
				*children[i] = FixedBits::concreteToAbstract(n);
				concretise(variables[i], *(children[i]), satSolverClause, beev, tosat.SATVar_to_SymbolIndexMap());
			}

			ASTNode n = (ce.GetCounterExample(true, outputNode));
			output = FixedBits::concreteToAbstract(n);
			//cerr << resultNode.GetName() << " " << n << endl;
			concretise(outputNode, output, satSolverClause, beev, tosat.SATVar_to_SymbolIndexMap());
		}
		else
		{
			for (int i = 0; i < numberOfChildren; i++)
			{
				ASTNode n = (ce.GetCounterExample(true, variables[i]));
				//cerr << variables[i].GetName() << " " << n << endl;
				*children[i] = FixedBits::meet(FixedBits::concreteToAbstract(n), *children[i]);
				concretise(variables[i], *(children[i]), satSolverClause, beev, tosat.SATVar_to_SymbolIndexMap());
			}

			ASTNode n = (ce.GetCounterExample(true, outputNode));
			output = FixedBits::meet(FixedBits::concreteToAbstract(n), output);
			//cerr << resultNode.GetName() << " " << n << endl;
			concretise(outputNode, output, satSolverClause, beev,tosat.SATVar_to_SymbolIndexMap());

		}

		first = false;

		if (satSolverClause.size() == 0)
		  break; // everything is at top.
	}

	beev->UserFlags.bitConstantProp_flag = !disabledProp;
	beev->UserFlags.print_output_flag = printOutput;
	beev->UserFlags.check_counterexample_flag= checkCounter;

	return first;
}
}
}
