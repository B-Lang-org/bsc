// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

/* Transform:
 *
 * Converts signed Div/signed remainder/signed modulus into their
 * unsigned counterparts. Removes array selects and stores from
 * formula. Arrays are replaced by equivalent bit-vector variables
 */
#include "ArrayTransformer.h"
#include <cassert>
#include "../simplifier/simplifier.h"
#include <cstdlib>
#include <cstdio>
#include <iostream>
#include <sstream>


namespace BEEV
{
  // NB: This is the only function that should be called
  // externally. It sets up the cache that the others use.
  ASTNode ArrayTransformer::TransformFormula_TopLevel(const ASTNode& form)
  {
    runTimes->start(RunTimes::Transforming);

    assert(TransformMap == NULL);
    assert(form.GetSTPMgr() == this->bm);
    TransformMap = new ASTNodeMap(100);
    ASTNode result = TransformFormula(form);

#if 0
    {
    	ASTNodeSet visited;
    	assertTransformPostConditions(result,visited);
    }
#endif

    TransformMap->clear();
    delete TransformMap;
    TransformMap = NULL;

    if (bm->UserFlags.stats_flag)
      printArrayStats();

    // This establishes equalities between every indexes, and a fresh variable.
    if (!bm->UserFlags.ackermannisation)
    {
		ASTNodeMap replaced;

		ASTVec equalsNodes;
		for (ArrayTransformer::ArrType::iterator
			   iset = arrayToIndexToRead.begin(),
			   iset_end = arrayToIndexToRead.end();
			 iset != iset_end; iset++)
		  {
				const ASTNode& ArrName = iset->first;
				map<ASTNode, ArrayTransformer::ArrayRead>& mapper = iset->second;

				for (map<ASTNode, ArrayTransformer::ArrayRead>::iterator it =mapper.begin() ; it != mapper.end();it++)
				{
					const ASTNode& the_index = it->first;

					if (the_index.isConstant() || the_index.GetKind() == SYMBOL)
					{
						it->second.index_symbol = the_index;
					}
					else if (replaced.find(the_index) != replaced.end()) // Already associated with a variable.
					{
						it->second.index_symbol = replaced.find(the_index)->second;
					}
					else
					{
						ASTNode newV = bm->CreateFreshVariable(0,the_index.GetValueWidth(), "STP__IndexVariables");
						equalsNodes.push_back(nf->CreateNode(EQ, the_index, newV));
						replaced.insert(make_pair(the_index,newV));
						it->second.index_symbol = newV;
					}
					assert(it->second.index_symbol.GetValueWidth() == the_index.GetValueWidth());
				}
		  }

		runTimes->stop(RunTimes::Transforming);

		if (equalsNodes.size() > 0)
			return nf->CreateNode(AND, result, equalsNodes);
		else
			return result;
    }
    else
    {
    	runTimes->stop(RunTimes::Transforming);
    	return result;
    }
  }

  //Translates signed BVDIV,BVMOD and BVREM into unsigned variety
  ASTNode ArrayTransformer::TranslateSignedDivModRem(const ASTNode& in,  NodeFactory* nf, STPMgr *bm)
  {
    assert(in.GetChildren().size() ==2);

    const ASTNode& dividend = in[0];
    const ASTNode& divisor = in[1];
    const unsigned len = in.GetValueWidth();

    ASTNode hi1 = bm->CreateBVConst(32, len - 1);
    ASTNode one = bm->CreateOneConst(1);
    ASTNode zero = bm->CreateZeroConst(1);
    // create the condition for the dividend
    ASTNode cond_dividend = 
      nf->CreateNode(EQ, one, nf->CreateTerm(BVEXTRACT, 1, dividend, hi1, hi1));
    // create the condition for the divisor
    ASTNode cond_divisor = 
      nf->CreateNode(EQ, one,
                     nf->CreateTerm(BVEXTRACT, 1, divisor, hi1, hi1));

    if (SBVREM == in.GetKind())
      {
        //BVMOD is an expensive operation. So have the fewest bvmods
        //possible. Just one.

        //Take absolute value.
        ASTNode pos_dividend = 
          nf->CreateTerm(ITE, len,
                         cond_dividend, 
                         nf->CreateTerm(BVUMINUS, len, dividend),
                         dividend);
        ASTNode pos_divisor = 
          nf->CreateTerm(ITE, len,
                         cond_divisor, 
                         nf->CreateTerm(BVUMINUS, len, divisor),
                         divisor);

        //create the modulus term
        ASTNode modnode = 
          nf->CreateTerm(BVMOD, len,
                         pos_dividend, pos_divisor);

        //If the dividend is <0 take the unary minus.
        ASTNode n = 
          nf->CreateTerm(ITE, len,
                         cond_dividend, 
                         nf->CreateTerm(BVUMINUS, len, modnode),
                         modnode);
        	return n;
      }

    // This is the modulus of dividing rounding to -infinity.
    else if (SBVMOD == in.GetKind())
      {

    	/*
			(bvsmod s t) abbreviates
				  (let ((?msb_s ((_ extract |m-1| |m-1|) s))
						(?msb_t ((_ extract |m-1| |m-1|) t)))
					(let ((abs_s (ite (= ?msb_s #b0) s (bvneg s)))
						  (abs_t (ite (= ?msb_t #b0) t (bvneg t))))
					  (let ((u (bvurem abs_s abs_t)))
						(ite (= u (_ bv0 m))
							 u
						(ite (and (= ?msb_s #b0) (= ?msb_t #b0))
							 u
						(ite (and (= ?msb_s #b1) (= ?msb_t #b0))
							 (bvadd (bvneg u) t)
						(ite (and (= ?msb_s #b0) (= ?msb_t #b1))
							 (bvadd u t)
							 (bvneg u))))))))
    	 */

        //Take absolute value.
        ASTNode pos_dividend = 
          nf->CreateTerm(ITE, len,
                         cond_dividend, 
                         nf->CreateTerm(BVUMINUS, len, dividend),
                         dividend);
        ASTNode pos_divisor = 
          nf->CreateTerm(ITE, len,
                         cond_divisor, 
                         nf->CreateTerm(BVUMINUS, len, divisor),
                         divisor);

        ASTNode urem_node = 
          nf->CreateTerm(BVMOD, len,
                         pos_dividend, pos_divisor);

        // If the dividend is <0, then we negate the whole thing.
        ASTNode rev_node = 
          nf->CreateTerm(ITE, len,
                         cond_dividend, 
                         nf->CreateTerm(BVUMINUS, len, urem_node),
                         urem_node);

        // if It's XOR <0, and it doesn't perfectly divide, then add t (not its absolute value).
        ASTNode xor_node = 
          nf->CreateNode(XOR, cond_dividend, cond_divisor);
        ASTNode neZ = nf->CreateNode(NOT, nf->CreateNode(EQ, rev_node, bm->CreateZeroConst(divisor.GetValueWidth())));
        ASTNode cond = nf->CreateNode(AND,xor_node ,neZ);
        ASTNode n = 
          nf->CreateTerm(ITE, len,
        		  cond,
                         nf->CreateTerm(BVPLUS, len, rev_node, divisor),
                         rev_node);

        	return n;
      }
    else if (SBVDIV == in.GetKind())
      {
        //now handle the BVDIV case
        //if topBit(dividend) is 1 and topBit(divisor) is 0
        //
        //then output is -BVDIV(-dividend,divisor)
        //
        //elseif topBit(dividend) is 0 and topBit(divisor) is 1
        //
        //then output is -BVDIV(dividend,-divisor)
        //
        //elseif topBit(dividend) is 1 and topBit(divisor) is 1
        //
        // then output is BVDIV(-dividend,-divisor)
        //
        //else simply output BVDIV(dividend,divisor)

        //Take absolute value.
        ASTNode pos_dividend = 
          nf->CreateTerm(ITE, len,
                         cond_dividend, 
                         nf->CreateTerm(BVUMINUS, len, dividend),
                         dividend);
        ASTNode pos_divisor = 
          nf->CreateTerm(ITE, len,
                         cond_divisor, 
                         nf->CreateTerm(BVUMINUS, len, divisor),
                         divisor);

        ASTNode divnode = 
          nf->CreateTerm(BVDIV, len, pos_dividend, pos_divisor);

        // A little confusing. Only negate the result if they are XOR <0.
        ASTNode xor_node = 
          nf->CreateNode(XOR, cond_dividend, cond_divisor);
        ASTNode n = 
          nf->CreateTerm(ITE, len,
                         xor_node, 
                         nf->CreateTerm(BVUMINUS, len, divnode),
                         divnode);

        	return n;
      }

    FatalError("TranslateSignedDivModRem:"\
               "input must be signed DIV/MOD/REM", in);
    return bm->ASTUndefined;

  }//end of TranslateSignedDivModRem()

  // Check that the transformations have occurred.
  void ArrayTransformer::assertTransformPostConditions(const ASTNode & term, ASTNodeSet& visited)
  {

	  // I haven't measure whether this is the quickest way to do it?
	  pair<ASTNodeSet::iterator, bool> p = visited.insert(term);
	  if (!p.second)
		  return;

    const Kind k = term.GetKind();

    // Check the array reads / writes have been removed
    assert( READ !=k );
    assert( WRITE !=k);

    // There should be no nodes left of type array.
    assert(0 == term.GetIndexWidth());

    const ASTVec& c = term.GetChildren();
    ASTVec::const_iterator it = c.begin();
    const ASTVec::const_iterator itend = c.end();
    for (; it != itend; it++)
      {
        assertTransformPostConditions(*it,visited);
      }
  }//End of assertTransformPostConditions()

  /********************************************************
   * TransformFormula()
   *
   * Get rid of DIV/MODs, ARRAY read/writes, FOR constructs
   ********************************************************/
  ASTNode ArrayTransformer::TransformFormula(const ASTNode& simpleForm)
  {
    assert(TransformMap != NULL);

    const Kind k = simpleForm.GetKind();
    if (!(is_Form_kind(k) && BOOLEAN_TYPE == simpleForm.GetType()))
      {
        //FIXME: "You have inputted a NON-formula"?
        FatalError("TransformFormula:"\
                   "You have input a NON-formula", simpleForm);
      }

    ASTNodeMap::const_iterator iter;
    if ((iter = TransformMap->find(simpleForm)) != TransformMap->end())
      return iter->second;

    ASTNode result;

    switch (k)
      {
      case TRUE:
      case FALSE:
        {
          result = simpleForm;
          break;
        }
      case NOT:
        {
          ASTVec c;
          c.push_back(TransformFormula(simpleForm[0]));
          result = nf->CreateNode(NOT, c);
          break;
        }
      case BVLT:
      case BVLE:
      case BVGT:
      case BVGE:
      case BVSLT:
      case BVSLE:
      case BVSGT:
      case BVSGE:
        {
          ASTVec c;
          c.push_back(TransformTerm(simpleForm[0]));
          c.push_back(TransformTerm(simpleForm[1]));
          result = nf->CreateNode(k, c);
          break;
        }
      case EQ:
        {
          ASTNode term1 = TransformTerm(simpleForm[0]);
          ASTNode term2 = TransformTerm(simpleForm[1]);
          if (bm->UserFlags.optimize_flag)
        	  result = simp->CreateSimplifiedEQ(term1, term2);
          else
        	  result = nf->CreateNode(EQ,term1, term2);
          break;
        }
      case AND: // These could shortcut. Not sure if the extra effort is justified.
      case OR:
      case NAND:
      case NOR:
      case IFF:
      case XOR:
      case ITE:
      case IMPLIES:
        {
          ASTVec vec;
          vec.reserve(simpleForm.Degree());

          for (ASTVec::const_iterator 
                 it = simpleForm.begin(), 
                 itend = simpleForm.end(); it != itend; it++)
            {
              vec.push_back(TransformFormula(*it));
            }

          result = nf->CreateNode(k, vec);
          break;
        }
      case PARAMBOOL:
        {
          //If the parameteric boolean variable is of the form
          //VAR(const), then convert it into a Boolean variable of the
          //form "VAR(const)".
          //
          //Else if the paramteric boolean variable is of the form
          //VAR(expression), then simply return it
          if(BVCONST == simpleForm[1].GetKind())
            {
              result = 
                bm->NewParameterized_BooleanVar(simpleForm[0],simpleForm[1]);
            }
          else
            {
              result = simpleForm;
            }
          break;
        }
      default:
        {
          if (k == SYMBOL && BOOLEAN_TYPE == simpleForm.GetType())
            result = simpleForm;
          else
            {
              FatalError("TransformFormula: Illegal kind: ", 
                         ASTUndefined, k);
              cerr << "The input is: " << simpleForm << endl;
              cerr << "The valuewidth of input is : " 
                   << simpleForm.GetValueWidth() << endl;
            }
          break;
        }
      } //end of Switch

    assert(!result.IsNull());
    if (simpleForm.Degree() > 0)
      (*TransformMap)[simpleForm] = result;
    return result;
  } //End of TransformFormula


  ASTNode ArrayTransformer::TransformTerm(const ASTNode& term)
  {
    assert(TransformMap != NULL);

    const Kind k = term.GetKind();
    if (!is_Term_kind(k))
      FatalError("TransformTerm: Illegal kind: You have input a nonterm:", 
                 term, k);
    ASTNodeMap::const_iterator iter;
    if ((iter = TransformMap->find(term)) != TransformMap->end())
      return iter->second;

    ASTNode result;
    switch (k)
      {
      case SYMBOL:
      case BVCONST:
      {
          result = term;
          break;
        }
      case WRITE:
        FatalError("TransformTerm: this kind is not supported", term);
        break;
      case READ:
        result = TransformArrayRead(term);
        break;
      case ITE:
        {
          ASTNode cond = term[0];
          ASTNode thn = term[1];
          ASTNode els = term[2];
          cond = TransformFormula(cond);
          if (ASTTrue == cond)
        	  result = TransformTerm(thn);
          else if (ASTFalse == cond)
        	  result = TransformTerm(els);
          else
          {
        	  thn = TransformTerm(thn);
        	  els = TransformTerm(els);
        	  if (bm->UserFlags.optimize_flag)
        		  result = simp->CreateSimplifiedTermITE(cond, thn, els);
        	  else
        		  result = nf->CreateTerm(ITE, thn.GetValueWidth(), cond, thn, els);
          }
          assert(result.GetIndexWidth() ==term.GetIndexWidth());
          break;
        }
      default:
        {
          const ASTVec& c = term.GetChildren();
          ASTVec::const_iterator it = c.begin();
          ASTVec::const_iterator itend = c.end();
          const unsigned width = term.GetValueWidth();
          const unsigned indexwidth = term.GetIndexWidth();
          ASTVec o;
          o.reserve(c.size());
          for (; it != itend; it++)
            {
              o.push_back(TransformTerm(*it));
            }

          if (c!=o)
          {
        	  result = nf->CreateArrayTerm(k,indexwidth, width, o);
          }
          else
        	  result = term;
        }
        break;
      }

    if (term.Degree() > 0)
      (*TransformMap)[term] = result;
    if (term.GetValueWidth() != result.GetValueWidth())
      FatalError("TransformTerm: "\
                 "result and input terms are of different length", result);
    if (term.GetIndexWidth() != result.GetIndexWidth())
      {
        cerr << "TransformTerm: input term is : " << term << endl;
        FatalError("TransformTerm: "\
                   "result & input terms have different index length", result);
      }
    return result;
  } //End of TransformTerm

  /* This function transforms Array Reads, Read over Writes, Read over
   * ITEs into flattened form.
   *
   * Transform1: Suppose there are two array reads in the input
   * Read(A,i) and Read(A,j) over the same array. Then Read(A,i) is
   * replaced with a symbolic constant, say v1, and Read(A,j) is
   * replaced with the following ITE:
   *
   * ITE(i=j,v1,v2)
   *
   */
  ASTNode ArrayTransformer::TransformArrayRead(const ASTNode& term)
  {
    assert(TransformMap != NULL);

    const unsigned int width = term.GetValueWidth();

    if (READ != term.GetKind())
      return term;

    ASTNodeMap::const_iterator iter;
    if ((iter = TransformMap->find(term)) != TransformMap->end())
      return iter->second;

    //'term' is of the form READ(arrName, readIndex)
    const ASTNode & arrName = term[0];
    const ASTNode & readIndex = TransformTerm(term[1]);

    ASTNode result;

    switch (arrName.GetKind())
      {
      case SYMBOL:
        {
          /* input is of the form: READ(A, readIndex)
           *
           * output is of the from: A1, if this is the first READ over A
           *
           *                        ITE(previous_readIndex=readIndex,A1,A2)
           *
           *                        .....
           */

          {
            ArrType::const_iterator it;
            if ((it = arrayToIndexToRead.find(arrName)) != arrayToIndexToRead.end())
              {
                map<ASTNode, ArrayRead>::const_iterator it2;
                  if ((it2 = it->second.find(readIndex)) != it->second.end())
                    {
                      result = it2->second.ite;
                      break;
                    }
              }
          }

          // Make up a new abstract variable. Build symbolic name
          // corresponding to array read. The symbolic name has 2
          // components: stringname, and a count

          ASTNode CurrentSymbol = bm->CreateFreshVariable(
                          term.GetIndexWidth(),
                          term.GetValueWidth(),
                          "array_" + string(arrName.GetName()));

          result = CurrentSymbol;

          if (!bm->UserFlags.ackermannisation)
            {
              // result is a variable here; it is an ite in the
              // else-branch
            }
          else
            {
              // Full Array transform if we're not doing read refinement.

              //list of array-read indices corresponding to arrName, seen while
              //traversing the AST tree. we need this list to construct the ITEs
              const arrTypeMap& new_read_Indices = arrayToIndexToRead[arrName];

              arrTypeMap::const_iterator it2 = new_read_Indices.begin();
              arrTypeMap::const_iterator it2end = new_read_Indices.end();
              for (; it2 != it2end; it2++)
                {
                  ASTNode cond =  simp->CreateSimplifiedEQ(readIndex, it2->first);
                  if (ASTFalse == cond)
                    continue;

                  if (ASTTrue == cond)
                    {
                      result = it2->second.ite;
                      break;
                    }

                  result =
                    simp->CreateSimplifiedTermITE(cond, it2->second.ite, result);
                }
            }

          assert(arrName.GetType() == ARRAY_TYPE);
          arrayToIndexToRead[arrName].insert(make_pair(readIndex,ArrayRead (result, CurrentSymbol)));
          break;
        } //end of READ over a SYMBOL
      case WRITE:
        {
          /* The input to this case is: READ((WRITE A i val) j)
           *
           * The output of this case is: ITE( (= i j) val (READ A j))
           */

          /* 1. arrName or term[0] is infact a WRITE(A,i,val) expression
           *
           * 2. term[1] is the read-index j
           *
           * 3. arrName[0] is the new arrName i.e. A. A can be either a
           SYMBOL or a nested WRITE. no other possibility
           *
           * 4. arrName[1] is the WRITE index i.e. i
           *
           * 5. arrName[2] is the WRITE value i.e. val (val can inturn
           *    be an array read)
           */

          ASTNode writeIndex = TransformTerm(arrName[1]);
          ASTNode writeVal = TransformTerm(arrName[2]);

          if (ARRAY_TYPE != arrName[0].GetType())
            FatalError("TransformArray: "\
                       "An array write is being attempted on a non-array:", 
                       term);

          //if ((SYMBOL == arrName[0].GetKind()
               //|| WRITE == arrName[0].GetKind()))
            {
              ASTNode cond = 
                simp->CreateSimplifiedEQ(writeIndex, readIndex);
              assert(BVTypeCheck(cond));

              // If the condition is true, it saves iteratively transforming through
              // all the (possibly nested) arrays.
              if (ASTTrue == cond)
              {
            	  result = writeVal;
              }
              else
              {
				  ASTNode readTerm =
					nf->CreateTerm(READ, width, arrName[0], readIndex);
				  assert(BVTypeCheck(readTerm));

				  // The simplifying node factory may have produced
				  // something that's not a READ.
				  ASTNode readPushedIn = TransformTerm(readTerm);
				  assert(BVTypeCheck(readPushedIn));

				  result =
					simp->CreateSimplifiedTermITE(cond, writeVal, readPushedIn);
              }
            }

            // Trevor: I've removed this code because I don't see the advantage in working
            // inside out. i.e. transforming read(write(ite(p,A,B),i,j),k), into
            // read(ite(p,write(A,i,j),write(B,i,j),k). That is bringing up the ite.
            // Without this code it will become: ite(i=k, j, read(ite(p,A,B),k))

            #if 0
          else if (ITE == arrName[0].GetKind())
            {
              // pull out the ite from the write // pushes the write
              // through.
              ASTNode writeTrue =
                nf->CreateNode(WRITE, (arrName[0][1]), writeIndex, writeVal);
              writeTrue.SetIndexWidth(writeIndex.GetValueWidth());
              writeTrue.SetValueWidth(writeVal.GetValueWidth());
              assert(ARRAY_TYPE == writeTrue.GetType());

              ASTNode writeFalse = 
                nf->CreateNode(WRITE, (arrName[0][2]), writeIndex, writeVal);
              writeFalse.SetIndexWidth(writeIndex.GetValueWidth());
              writeFalse.SetValueWidth(writeVal.GetValueWidth());
              assert(ARRAY_TYPE == writeFalse.GetType());

              result =  (writeTrue == writeFalse) ?
                writeTrue : simp->CreateSimplifiedTermITE(TransformFormula(arrName[0][0]),
                                              writeTrue, writeFalse);
              result.SetIndexWidth(writeIndex.GetValueWidth());
              result.SetValueWidth(writeVal.GetValueWidth());
              assert(ARRAY_TYPE == result.GetType());

              result = 
                nf->CreateTerm(READ, writeVal.GetValueWidth(),
                               result, readIndex);
              BVTypeCheck(result);
              result = TransformArrayRead(result);
            }
          else
            FatalError("TransformArray: Write over bad type.");
	#endif
          break;
        } //end of READ over a WRITE
      case ITE:
        {
          /* READ((ITE cond thn els) j)
           *
           * is transformed into
           *
           * (ITE cond (READ thn j) (READ els j))
           */

          // pull out the ite from the read // pushes the read through.

          //(ITE cond thn els)

          ASTNode cond = arrName[0];
          cond = TransformFormula(cond);

          const ASTNode& thn = arrName[1];
          const ASTNode& els = arrName[2];

		  //(READ thn j)
		  ASTNode thnRead = nf->CreateTerm(READ, width, thn, readIndex);
		  assert(BVTypeCheck(thnRead));

		  //(READ els j)
		  ASTNode elsRead = nf->CreateTerm(READ, width, els, readIndex);
		  assert(BVTypeCheck(elsRead));

		  /* We try to call TransformTerm only if necessary, because it
		   * introduces a new symbol for each read. The amount of work we
		   * need to do later is based on the square of the number of symbols.
		   */
          if (ASTTrue == cond)
          {
			  result = TransformTerm(thnRead);
          }
          else if (ASTFalse == cond)
          {
			  result = TransformTerm(elsRead);
          }
          else
          {
			  thnRead = TransformTerm(thnRead);
			  elsRead = TransformTerm(elsRead);

			  //(ITE cond (READ thn j) (READ els j))
			  result = simp->CreateSimplifiedTermITE(cond, thnRead, elsRead);
		  }
          break;
        }
      default:
        FatalError("TransformArray: "\
                   "The READ is NOT over SYMBOL/WRITE/ITE", term);
        break;
      }

    assert(BVTypeCheck(result));
    assert(!result.IsNull());
    (*TransformMap)[term] = result;
    return result;
  } //end of TransformArray()


  //Since these arrayreads are being nuked and recorded in the
  //substitutionmap, we have to also record the fact that each
  //arrayread (e0 is of the form READ(Arr,const) here is represented
  //by a BVCONST (e1). This is necessary for later Leibnitz Axiom
  //generation
  void ArrayTransformer::FillUp_ArrReadIndex_Vec(const ASTNode& e0, 
                                                 const ASTNode& e1)
  {
      assert (e0.GetKind() == READ);
      assert (e0[0].GetKind() == SYMBOL);
      assert (e0[1].GetKind() == BVCONST);
      assert (e1.GetKind() == BVCONST);
      assert(arrayToIndexToRead[e0[0]].find(e0[1]) ==arrayToIndexToRead[e0[0]].end());

      arrayToIndexToRead[e0[0]].insert(make_pair(e0[1],ArrayRead (e1, e1)));
  }


} //end of namespace BEEV
