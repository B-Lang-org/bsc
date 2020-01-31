// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/


#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "bvsolver.h"

//This file contains the implementation of member functions of
//bvsolver class, which represents the bitvector arithmetic linear
//solver. Please also refer the STP's CAV 2007 paper for the
//complete description of the linear solver algorithm
//
//The bitvector solver is a partial solver, i.e. it does not solve
//for all variables in the system of equations. it is
//best-effort. it relies on the SAT solver to be complete.
//
//The BVSolver assumes that the input equations are normalized, and
//have liketerms combined etc. It won't fail if the input isn't
// normalised. It just won't be able to simplify things, for example
// it cant simplify (3*3)*x = y.
//
//0. Traverse top-down over the input DAG, looking for a conjunction
//0. of equations. if you find one, then for each equation in the
//0. conjunction, do the following steps.
//
//1. check for Linearity of the input equation
//
//2. Solve for a "chosen" variable. The variable should occur
//2. exactly once and must have an odd coeff. Refer STP's CAV 2007
//2. paper for actual solving procedure
//
//4. Outside the solver, Substitute and Re-normalize the input DAG
namespace BEEV
{
	const bool flatten_ands = true;
	const bool sort_extracts_last = false;
	const bool debug_bvsolver = false;

	// The simplify functions can increase the size of the DAG,
	// so we have the option to disable simplifications.
  ASTNode BVSolver::simplifyNode(const ASTNode n)
  {
	  if (!simplify)
		  return n;

	  if (n.GetType() == BOOLEAN_TYPE)
		  return _simp->SimplifyFormula(n,false,NULL);
	  else
		  return _simp->SimplifyTerm(n);
  }


  //check the solver map for 'key'. If key is present, then return the
  //value by reference in the argument 'output'
  bool BVSolver::CheckAlreadySolvedMap(const ASTNode& key, ASTNode& output)
  {
    ASTNodeMap::const_iterator it;
    if ((it = FormulasAlreadySolvedMap.find(key)) 
        != FormulasAlreadySolvedMap.end())
      {
        output = it->second;
        return true;
      }
    return false;
  } //CheckAlreadySolvedMap()

  void BVSolver::UpdateAlreadySolvedMap(const ASTNode& key, 
                                        const ASTNode& value)
  {
    assert(key.GetType() == BOOLEAN_TYPE);
	  FormulasAlreadySolvedMap[key] = value;
  } //end of UpdateAlreadySolvedMap()

  //accepts an even number "in", and returns the location of
  // the lowest bit that is turned on in that number.
  void BVSolver::SplitEven_into_Oddnum_PowerOf2(const ASTNode& in,
  		unsigned int& number_shifts) {
  	assert (BVCONST == in.GetKind() && !_simp->BVConstIsOdd(in));

  	// location of the least significant bit turned on.
  	for (number_shifts = 0; number_shifts < in.GetValueWidth()
  			&& !CONSTANTBV::BitVector_bit_test(in.GetBVConst(), number_shifts); number_shifts++) {
  	};
  	assert(number_shifts >0); // shouldn't be odd.
  }

  //chooses a variable in the lhs and returns the chosen variable
  ASTNode BVSolver::ChooseMonom(const ASTNode& eq, ASTNode& modifiedlhs, ASTNodeSet& checked)
  {
	  assert(EQ == eq.GetKind());
	  assert(BVPLUS == eq[0].GetKind() || BVPLUS== eq[1].GetKind());

	// Unfortunately, the bvsolver is written to expect nodes in the
	// reverse order to how the simplifying node factory produces them.
	// That is, the simplifying node factory sorts by arithless, i.e.
	// with constants or symbols on the left.
    const bool lhsIsPlus = (BVPLUS == eq[0].GetKind());
    const ASTNode& lhs = lhsIsPlus? eq[0] : eq[1];
    const ASTNode& rhs = lhsIsPlus? eq[1] : eq[0];

    assert(BVPLUS == lhs.GetKind());

    //collect all the vars in the lhs and rhs
    vars.getSymbol(eq);

    //handle BVPLUS case
    ASTVec c = FlattenKind(BVPLUS, lhs.GetChildren());
    ASTVec o;
    ASTNode outmonom = ASTUndefined;
    bool chosen_symbol = false;

    //choose variables with no coeffs
    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
    	const ASTNode& monom = *it;
        if (
        	(
        	SYMBOL == monom.GetKind()
            && !chosen_symbol
       		&& checked.find(monom)==checked.end()
            && !vars.VarSeenInTerm(monom,rhs)
            )
            ||
            (
             BVUMINUS == monom.GetKind()
             && SYMBOL == monom[0].GetKind()
             && !chosen_symbol
             && checked.find(monom[0])==checked.end()
             && !vars.VarSeenInTerm(monom[0],rhs)
            )
           )
        {
        	// Look through all the children of the BVPLUS and check
        	// that the variable appears in none of them.

        	ASTNode var = (SYMBOL == monom.GetKind())? monom: monom[0];
        	bool duplicated = false;
        	for (ASTVec::const_iterator it2 = c.begin(); it2 != itend; it2++)
			{
				if (it2 == it)
					continue;
				if (vars.VarSeenInTerm(var,*it2))
				{
					duplicated = true;
					break;
				}
			}
			if (!duplicated)
			{
				outmonom = monom; //nb. monom not var.
				chosen_symbol = true;
				checked.insert(var);
			}
			else
				o.push_back(monom);
        }
    	else
    		o.push_back(monom);
	}

    //try to choose only odd coeffed variables first
    if (!chosen_symbol)
      {
        ASTNode zero = _bm->CreateZeroConst(32);

    	o.clear();
        for (ASTVec::const_iterator
               it = c.begin(), itend = c.end(); it != itend; it++)
          {
            const ASTNode& monom = *it;
            ASTNode var = 
              (BVMULT == monom.GetKind()) ? 
              monom[1] : 
              ASTUndefined;

            if (BVMULT == monom.GetKind() 
                && BVCONST == monom[0].GetKind() 
                && _simp->BVConstIsOdd(monom[0]) 
                && !chosen_symbol
                && checked.find(var)==checked.end()
                && ((SYMBOL == var.GetKind() 
                     && !vars.VarSeenInTerm(var,rhs)
                    )
                    || (BVEXTRACT == var.GetKind() 
                        && SYMBOL == var[0].GetKind() 
                        && BVCONST == var[1].GetKind() 
                        && zero == var[2]
                        && !vars.VarSeenInTerm(var[0],rhs)
                        ))
                )
              {
                //monom[0] is odd.
                outmonom = monom;
                chosen_symbol = true;
                checked.insert(var);
              }
            else if (
                !chosen_symbol
                && monom.GetKind() == BVEXTRACT
                && SYMBOL == monom[0].GetKind()
                && BVCONST == monom[1].GetKind()
                && zero == monom[2]
                && checked.find(monom[0])==checked.end()
                && !vars.VarSeenInTerm(monom[0],rhs)
            )
              {
              outmonom = monom;
              chosen_symbol = true;
              checked.insert(monom[0]);
              }
            else if (
                       !chosen_symbol
                       && monom.GetKind() == BVUMINUS
                       && monom[0].GetKind() == BVEXTRACT
                       && SYMBOL == monom[0][0].GetKind()
                       && BVCONST == monom[0][1].GetKind()
                       && zero == monom[0][2]
                       && checked.find(monom[0][0])==checked.end()
                       && !vars.VarSeenInTerm(monom[0][0],rhs)
                   )
                     {
                     outmonom = monom;
                     chosen_symbol = true;
                     checked.insert(monom[0][0]);
                     }
            else

              {
                o.push_back(monom);
              }
          }
      }

    modifiedlhs = 
      (o.size() > 1) ? 
      _bm->CreateTerm(BVPLUS, lhs.GetValueWidth(), o) : 
      o[0];

    if (debug_bvsolver)
      {
        cerr << "Initial:" << eq;
        cerr << "Chosen Monomial:" << outmonom;
        cerr << "Output LHS:" << modifiedlhs;
      }

    // can be SYMBOL or (BVUMINUS SYMBOL) or (BVMULT ODD_BVCONST SYMBOL) or
    // (BVMULT ODD_BVCONST (EXTRACT SYMBOL BV_CONST ZERO)) or
    // BVUMINUS (EXTRACT SYMBOL BV_CONST ZERO) or
    // (EXTRACT SYMBOL BV_CONST ZERO)
    return outmonom;
  } //end of choosemonom()

  // Manipulate the lhs and rhs to get just a variable on the lhs (if possible). Then add to the
  // substitution map.
  ASTNode BVSolver::substitute(const ASTNode& eq, const ASTNode& lhs, const ASTNode& rhs, const bool single)
  {

  ASTNode output;

  switch (lhs.GetKind())
    {
    case SYMBOL:
      {
        //input is of the form x = rhs first make sure that the lhs
        //symbol does not occur on the rhs or that it has not been
        //solved for
        if (!single && vars.VarSeenInTerm(lhs, rhs))
          {
            //found the lhs in the rhs. Abort!
            return eq;
          }

        if (!_simp->UpdateSolverMap(lhs, rhs))
          {
            return eq;
          }

        output = ASTTrue;
        break;
      }

    case BVEXTRACT:
      {
        const ASTNode zero = _bm->CreateZeroConst(32);

        if (!(SYMBOL == lhs[0].GetKind()
              && BVCONST == lhs[1].GetKind()
              && zero == lhs[2]
              && !vars.VarSeenInTerm(lhs[0], rhs)
              ))
          {
            return eq;
          }

        if (vars.VarSeenInTerm(lhs[0], rhs))
          {
            return eq;
          }

        if (!_simp->UpdateSolverMap(lhs, rhs))
          {
            return eq;
          }

        if (lhs[0].GetValueWidth() != lhs.GetValueWidth())
        {
        //if the extract of x[i:0] = t is entered into the solvermap,
        //then also add another entry for x = x1@t
        ASTNode var = lhs[0];
        ASTNode newvar =
          _bm->CreateFreshVariable(0, var.GetValueWidth() - lhs.GetValueWidth(), "v_solver");
        newvar =
          _bm->CreateTerm(BVCONCAT, var.GetValueWidth(), newvar, rhs);
                        assert(BVTypeCheck(newvar));
        _simp->UpdateSolverMap(var, newvar);
        }
        else
                _simp->UpdateSolverMap(lhs[0], rhs);
        output = ASTTrue;
        break;
      }
    case BVMULT:
      {
        //the input is of the form a*x = t. If 'a' is odd, then compute
        //its multiplicative inverse a^-1, multiply 't' with it, and
        //update the solver map
        if (BVCONST != lhs[0].GetKind())
          {
            return eq;
          }

        if (!(SYMBOL == lhs[1].GetKind()
              || (BVEXTRACT == lhs[1].GetKind()
                  && SYMBOL == lhs[1][0].GetKind())))
          {
            return eq;
          }

        bool ChosenVar_Is_Extract =
          (BVEXTRACT == lhs[1].GetKind());

        //if coeff is even, then we know that all the coeffs in the eqn
        //are even. Simply return the eqn
        if (!_simp->BVConstIsOdd(lhs[0]))
          {
            return eq;
          }

        ASTNode a = _simp->MultiplicativeInverse(lhs[0]);
        ASTNode chosenvar =
                        ChosenVar_Is_Extract ? lhs[1][0] : lhs[1];
        ASTNode chosenvar_value =
                        simplifyNode(_bm->CreateTerm(BVMULT,
                                              rhs.GetValueWidth(),
                                              a, rhs));

        //if chosenvar is seen in chosenvar_value then abort
        if (vars.VarSeenInTerm(chosenvar, chosenvar_value))
          {
            //abort solving
            return eq;
          }

        // It fails if it's a full-bitwidth extract. These are rare, and won't be
        // present after simplification. So ignore them for now.
        if (ChosenVar_Is_Extract && lhs[0].GetValueWidth() == lhs.GetValueWidth())
                return eq;

        //found a variable to solve
        chosenvar = lhs[1];
        if (!_simp->UpdateSolverMap(chosenvar, chosenvar_value))
          {
            return eq;
          }

        if (ChosenVar_Is_Extract)
          {
            const ASTNode& var = lhs[1][0];

                                ASTNode newvar =
                                        _bm->CreateFreshVariable(0, var.GetValueWidth() - lhs[1].GetValueWidth(), "v_solver");
                                newvar =
                                      _bm->CreateTerm(BVCONCAT,
                                                                      var.GetValueWidth(),
                                                                      newvar, chosenvar_value);
                                assert(BVTypeCheck(newvar));
                                _simp->UpdateSolverMap(var, newvar);

          }
        output = ASTTrue;
        break;
      }
    default:
      output = eq;
      break;
    }
  return output;
  }

  //solver function which solves for variables with odd coefficient
  ASTNode BVSolver::BVSolve_Odd(const ASTNode& input)
  {
    ASTNode eq = input;
    //cerr << "Input to BVSolve_Odd()" << eq << endl;
    if (!(EQ == eq.GetKind()))
      {
        return input;
      }

    ASTNode output = input;

    //get the lhs and the rhs, and case-split on the lhs kind
    ASTNode lhs = eq[0];
    ASTNode rhs = eq[1];


	if (
			((BVCONST == lhs.GetKind()) && (BVCONST != rhs.GetKind()))  || // if only one side is a constant, it should be on the RHS.
			((SYMBOL == rhs.GetKind()) &&  (SYMBOL != lhs.GetKind()))  // If there is only one variable. It should be on the left.
	)
			{
		lhs = eq[1];
		rhs = eq[0];
		eq = _bm->CreateNode(EQ, lhs, rhs); // If "return eq" is called, return the arguments in the correct order.
		assert(BVTypeCheck(eq));
	}

    if (CheckAlreadySolvedMap(eq, output))
      {
        return output;
      }

    // ChooseMonom makes sure that the the LHS is not contained on the RHS, so we
    // set this "single" to true in the branch that runs chooseMonomial.
    bool single = false;

    if (BVPLUS == lhs.GetKind())
      {

        ASTNodeSet checked;
        do
        {
         ASTNode chosen_monom = ASTUndefined;
          ASTNode leftover_lhs;

          //choose monom makes sure that it gets only those vars that
          //occur exactly once in lhs and rhs put together
          chosen_monom = ChooseMonom(eq, leftover_lhs,checked);
          if (chosen_monom == ASTUndefined)
            {
              //no monomial was chosen
              return eq;
            }

          //if control is here then it means that a monom was chosen
          //
          //construct:  rhs - (lhs without the chosen monom)
          unsigned int len = lhs.GetValueWidth();
          leftover_lhs = simplifyNode(_bm->CreateTerm(BVUMINUS,len, leftover_lhs));
          assert(BVTypeCheck(leftover_lhs));
          rhs = simplifyNode(_bm->CreateTerm(BVPLUS, len, rhs, leftover_lhs));
          assert(BVTypeCheck(rhs));
          lhs = chosen_monom;
          single = true;
          //This tries to substitute it.. But it might not work, in which case it will return eq.
          output = substitute(eq, lhs, rhs,single);
        }
        while (output == eq);

      } //end of if(BVPLUS ...)

    else if (BVUMINUS == lhs.GetKind())
      {
        //equation is of the form (-lhs0) = rhs
        ASTNode lhs0 = lhs[0];
        rhs = simplifyNode(_bm->CreateTerm(BVUMINUS, rhs.GetValueWidth(), rhs));
        assert(BVTypeCheck(rhs));
        lhs = lhs0;
        output = substitute(eq, lhs, rhs,single);
      }
    else
      output = substitute(eq, lhs, rhs,single);

    UpdateAlreadySolvedMap(input, output);
    return output;
  } //end of BVSolve_Odd()


  //The toplevel bvsolver(). Checks if the formula has already been
  //solved. If not, the solver() is invoked. If yes, then simply drop
  //the formula
  ASTNode BVSolver::TopLevelBVSolve(const ASTNode& _input, const bool enable_simplify)
  {
      assert (_bm->UserFlags.wordlevel_solve_flag);
	  ASTNode input = _input;
	  simplify = enable_simplify;

    ASTNode output = input;
    if (CheckAlreadySolvedMap(input, output))
      {
        //output is TRUE. The formula is thus dropped
        return output;
      }

    Kind k = input.GetKind();

    if (!(EQ == k || AND == k))
      {
        return input;
      }

    if (flatten_ands && AND == k)
    {
        ASTVec c = FlattenKind(AND,input.GetChildren());
        input = _bm->CreateNode(AND,c);
        k = input.GetKind();

        // When flattening simplifications will be applied to the node, potentially changing it's type:
        // (AND x (ANY (not x) y)) gives us FALSE.
       if (!(EQ == k || AND == k ))
           return input;

          if (CheckAlreadySolvedMap(input, output))
            {
              //output is TRUE. The formula is thus dropped
              return output;
            }
    }

    _bm->GetRunTimes()->start(RunTimes::BVSolver);
    ASTVec o;
    ASTVec c;
    if (EQ == k)
      c.push_back(input);
    else
      c = input.GetChildren();

    ASTVec eveneqns;
    bool any_solved = false;
    for (ASTVec::iterator it = c.begin(), itend = c.end(); it != itend; it++)
      {
		 /*
    	 Calling applySubstitutionMapUntilArrays makes the required substitutions. For instance, if
    	 first was : v = x,
    	 then if the next formula is: x = v
    	 calling applySubstitutionMapUntilArrays on the second formula will convert it into "true", avoiding a cycle.

    	 The problem with this is that applySubstitutionMapUntilArrays() doesn't normally simplify into array
    	 operations. So given something like :
    	 a = b
    	 b = write(A,a,a)

    	 It will replace (a=b) with true, and store (a=b) in the solverMap. Then it will
    	 store b = write(A,a,a) in the solver map. Which is wrong. What it should do is
    	 rewrite a=b through the second expression, giving:
    	 b = write(A,b,b),
    	 which shouldn't be simplified.
  	   */

    	ASTNode aaa =  (any_solved && EQ == it->GetKind()) ? simplifyNode
    			(_simp->applySubstitutionMapUntilArrays(*it)) : *it;

        if (ASTFalse == aaa)
        {
        	_bm->GetRunTimes()->stop(RunTimes::BVSolver);
        	return ASTFalse; // shortcut. It's unsatisfiable.
        }
        aaa = BVSolve_Odd(aaa);

        bool even = false;
        aaa = CheckEvenEqn(aaa, even);
        if (even)
          {
            eveneqns.push_back(aaa);
          }
        else
          {
            if (ASTTrue != aaa)
              {
                o.push_back(aaa);
              }
          }
        if (ASTTrue == aaa)
        	{
               any_solved=true;
        	}
      }

    ASTNode evens;
    if (eveneqns.size() > 0)
      {
        //if there is a system of even equations then solve them
        evens =
          (eveneqns.size() > 1) ? 
          _bm->CreateNode(AND, eveneqns) : 
          eveneqns[0];
        //evens = _simp->SimplifyFormula(evens,false);
        evens = BVSolve_Even(evens);
        _bm->ASTNodeStats("Printing after evensolver:", evens);
      }
    else
      {
        evens = ASTTrue;
      }
    output = 
      (o.size() > 0) ? 
      ((o.size() > 1) ? 
       nf->CreateNode(AND, o) :
       o[0]) : 
      ASTTrue;
    if (evens != ASTTrue)
      output = nf->CreateNode(AND, output, evens);

    //if (_bm->UserFlags.isSet("xor-solve","1"))
    //  output = solveForAndOfXOR(output);

    // Imagine in the last conjunct A is replaced by B. But there could
    // be variable A's in the first conjunct. This gets rid of 'em.
    if (_simp->hasUnappliedSubstitutions())
      {
          output = _simp->applySubstitutionMap(output);
          _simp->haveAppliedSubstitutionMap();
      }

    UpdateAlreadySolvedMap(_input, output);
    _bm->GetRunTimes()->stop(RunTimes::BVSolver);
    return output;
  } //end of TopLevelBVSolve()

  ASTNode BVSolver::CheckEvenEqn(const ASTNode& input, bool& evenflag)
  {
    ASTNode eq = input;
    //cerr << "Input to BVSolve_Odd()" << eq << endl;
    if (!(EQ == eq.GetKind()))
      {
        evenflag = false;
        return eq;
      }

    const ASTNode zero = _bm->CreateZeroConst(eq[0].GetValueWidth());

    //lhs must be a BVPLUS, and rhs must be a BVCONST
	const bool lhsIsPlus = (BVPLUS == eq[0].GetKind());
	 ASTNode lhs = lhsIsPlus? eq[0] : eq[1];
	 ASTNode rhs = lhsIsPlus? eq[1] : eq[0];

    if (!(BVPLUS == lhs.GetKind() && zero == rhs))
      {
        evenflag = false;
        return eq;
      }

    const ASTVec& lhs_c = lhs.GetChildren();
    ASTNode savetheconst = rhs;
    for (ASTVec::const_iterator
           it = lhs_c.begin(), itend = lhs_c.end(); it != itend; it++)
      {
        const ASTNode aaa = *it;
        const Kind itk = aaa.GetKind();

        if (BVCONST == itk)
          {
            assert(savetheconst == rhs); // Returns the wrong result if there are >1 constants.

            //check later if the constant is even or not
            savetheconst = aaa;
            continue;
          }

        if (!(BVMULT == itk 
              && BVCONST == aaa[0].GetKind() 
              && SYMBOL == aaa[1].GetKind() 
              && !_simp->BVConstIsOdd(aaa[0])))
          {
            //If the monomials of the lhs are NOT of the form 'a*x' where
            //'a' is even, then return the false
            evenflag = false;
            return eq;
          }
      }//end of for loop

    //if control is here then it means that all coeffs are even. the
    //only remaining thing is to check if the constant is even or not
    if (_simp->BVConstIsOdd(savetheconst))
      {
        //the constant turned out to be odd. we have UNSAT eqn
        evenflag = false;
        return ASTFalse;
      }

    //all is clear. the eqn in even, through and through
    evenflag = true;
    return eq;
  } //end of CheckEvenEqn

  //solve an eqn whose monomials have only even coefficients
  ASTNode BVSolver::BVSolve_Even(const ASTNode& input)
  {

    if (!(EQ == input.GetKind() || AND == input.GetKind()))
      {
        return input;
      }

    ASTNode output;
    if (CheckAlreadySolvedMap(input, output))
      {
        return output;
      }

    ASTVec input_c;
    if (EQ == input.GetKind())
      {
        input_c.push_back(input);
      }
    else
      {
        input_c = input.GetChildren();
      }

    //power_of_2 holds the exponent of 2 in the coeff
    unsigned int power_of_2 = 0;
    //we need this additional variable to find the lowest power of 2
    unsigned int power_of_2_lowest = ~0;
    //the monom which has the least power of 2 in the coeff
    //ASTNode monom_with_best_coeff;
    for (ASTVec::iterator 
           jt = input_c.begin(), jtend = input_c.end(); 
         jt != jtend; jt++)
      {
        ASTNode eq = *jt;
        assert(EQ == eq.GetKind());

  	  const bool lhsIsPlus = (BVPLUS == eq[0].GetKind());
       ASTNode lhs = lhsIsPlus? eq[0] : eq[1];
       ASTNode rhs = lhsIsPlus? eq[1] : eq[0];


        ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
        //lhs must be a BVPLUS, and rhs must be a BVCONST
        if (!(BVPLUS == lhs.GetKind() && zero == rhs))
          {
            return input;
          }

        const ASTVec& lhs_c = lhs.GetChildren();
        for (ASTVec::const_iterator
               it = lhs_c.begin(), itend = lhs_c.end(); 
             it != itend; it++)
          {
            const ASTNode aaa = *it;
            const Kind itk = aaa.GetKind();
            if (!(BVCONST == itk 
                  && !_simp->BVConstIsOdd(aaa)) 
                && !(BVMULT == itk 
                     && BVCONST == aaa[0].GetKind() 
                     && SYMBOL == aaa[1].GetKind()
                     && !_simp->BVConstIsOdd(aaa[0])))
              {
                //If the monomials of the lhs are NOT of the form 'a*x' or 'a'
                //where 'a' is even, then return the eqn
                return input;
              }

            //we are gauranteed that if control is here then the monomial is
            //of the form 'a*x' or 'a', where 'a' is even
            ASTNode coeff = (BVCONST == itk) ? aaa : aaa[0];
            SplitEven_into_Oddnum_PowerOf2(coeff, power_of_2);
            if (power_of_2 < power_of_2_lowest)
              {
                power_of_2_lowest = power_of_2;
                //monom_with_best_coeff = aaa;
              }
            power_of_2 = 0;
          }//end of inner for loop
      } //end of outer for loop

    //get the exponent
    power_of_2 = power_of_2_lowest;
    assert(power_of_2 > 0);

    //if control is here, we are gauranteed that we have chosen a
    //monomial with fewest powers of 2
    ASTVec formula_out;
    for (ASTVec::iterator 
           jt = input_c.begin(), jtend = input_c.end(); jt != jtend; jt++)
      {
        ASTNode eq = *jt;

        // Want the plus on the lhs.
      	  const bool lhsIsPlus = (BVPLUS == eq[0].GetKind());
          ASTNode lhs = lhsIsPlus? eq[0] : eq[1];
          ASTNode rhs = lhsIsPlus? eq[1] : eq[0];

        ASTNode zero = _bm->CreateZeroConst(rhs.GetValueWidth());
        //lhs must be a BVPLUS, and rhs must be a BVCONST
        if (!(BVPLUS == lhs.GetKind() && zero == rhs))
          {
            return input;
          }

        unsigned len = lhs.GetValueWidth();
        ASTNode hi = _bm->CreateBVConst(32, len - 1);
        ASTNode low = _bm->CreateBVConst(32, len - power_of_2);
        ASTNode low_minus_one = _bm->CreateBVConst(32, len - power_of_2 - 1);
        ASTNode low_zero = _bm->CreateZeroConst(32);
        unsigned newlen = len - power_of_2;
        ASTNode two_const = _bm->CreateTwoConst(len);

        unsigned count = power_of_2;
        ASTNode two = two_const;
        while (--count)
          {
            two = 
              _simp->BVConstEvaluator(_bm->CreateTerm(BVMULT, 
                                                      len, 
                                                      two_const, 
                                                      two));
          }
        const ASTVec& lhs_c = lhs.GetChildren();
        ASTVec lhs_out;
        for (ASTVec::const_iterator
               it = lhs_c.begin(), itend = lhs_c.end(); 
             it != itend; it++)
          {
            ASTNode aaa = *it;
            const Kind itk = aaa.GetKind();
            if (BVCONST == itk)
              {
                aaa = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVDIV, 
                                                          len, 
                                                          aaa, two));
                aaa = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, 
                                                          newlen, 
                                                          aaa, 
                                                          low_minus_one, 
                                                          low_zero));
              }
            else
              {
                //it must be of the form a*x
                ASTNode coeff = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVDIV, 
                                                          len, 
                                                          aaa[0], two));
                coeff = 
                  _simp->BVConstEvaluator(_bm->CreateTerm(BVEXTRACT, 
                                                          newlen, 
                                                          coeff, 
                                                          low_minus_one, 
                                                          low_zero));
                ASTNode lower_x =
                		simplifyNode(_bm->CreateTerm(BVEXTRACT,
                                                      newlen, 
                                                      aaa[1], 
                                                      low_minus_one, 
                                                      low_zero));
                aaa = _bm->CreateTerm(BVMULT, newlen, coeff, lower_x);
              }
            lhs_out.push_back(aaa);
          }//end of inner forloop()
        rhs = _bm->CreateZeroConst(newlen);
        lhs = _bm->CreateTerm(BVPLUS, newlen, lhs_out);
        formula_out.push_back(_simp->CreateSimplifiedEQ(lhs, rhs));
      } //end of outer forloop()

    output = 
      (formula_out.size() > 0) ? 
      (formula_out.size() > 1) ? 
      _bm->CreateNode(AND, formula_out) : 
      formula_out[0] : 
      ASTTrue;

    UpdateAlreadySolvedMap(input, output);
    return output;
  } //end of BVSolve_Even()
};//end of namespace BEEV
