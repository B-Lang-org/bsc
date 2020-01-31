/*
 * This takes the topmost propositional part of the input, simplifies it with DAG aware rewritting,
 * then converts it back to ASTNodes.
 *
 *
 *  This has two problems: 1) It doesn't consider that the propositional variables that are introduced,
 *  might actually represent many thousands of AIG nodes, so it doesn't do the "DAG aware" part correctly.
 *  2) The startup of the DAR takes about 150M instructions, which is agggeeesss for small problems.
 */

#ifndef AIGSIMPLIFYPROPOSITIONALCORE_H_
#define AIGSIMPLIFYPROPOSITIONALCORE_H_

#include "../AST/AST.h"
#include "../STPManager/STPManager.h"
#include "simplifier.h"
#include "../extlib-abc/aig.h"
#include "../extlib-abc/dar.h"
#include "../to-sat/AIG/BBNodeManagerAIG.h"
#include "../to-sat/BitBlaster.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
class AIGSimplifyPropositionalCore : boost::noncopyable
{

	ASTNodeMap varToNodeMap;
	STPMgr * bm;
	NodeFactory* nf;

public:
	AIGSimplifyPropositionalCore(STPMgr *_bm)
	{
		bm = _bm;
		nf = _bm->defaultNodeFactory;
	}


private:

	// Convert theory nodes to fresh variables.
	ASTNode theoryToFresh(const ASTNode& n, ASTNodeMap& fromTo )
	{
		if (n.isConstant())
			return n;

		const Kind k = n.GetKind();
		if (k == SYMBOL)
			return n;

		ASTNodeMap::const_iterator it;
		if ((it = fromTo.find(n)) != fromTo.end())
			return it->second;

		assert(n.GetValueWidth() ==0);
		assert(n.GetIndexWidth() ==0);

		if (k == BVGT || k == BVGE || k == EQ || k == BVSGE || k == BVSGT || k == PARAMBOOL) // plus the rest.
		{
			ASTNode fresh = bm->CreateFreshVariable(n.GetIndexWidth(), n.GetValueWidth(),"theoryToFresh");
			varToNodeMap.insert(make_pair(fresh,n));
			fromTo.insert(make_pair(n,fresh));
			return fresh;
		}

		const ASTVec& children = n.GetChildren();
		ASTVec new_children;
		new_children.reserve(children.size());

		for (ASTVec::const_iterator it = children.begin(); it != children.end(); it++)
			new_children.push_back(theoryToFresh(*it,fromTo));

		ASTNode result;

		if (children != new_children)
			result = nf->CreateNode(k,new_children);
		else
			result = n;

		fromTo.insert(make_pair(n,result));
		return result;
	}

	typedef map<Aig_Obj_t *, ASTNode> cacheType;

	// Convert the AIG back to an ASTNode.
	ASTNode convert (BBNodeManagerAIG& mgr, Aig_Obj_t * obj, cacheType& cache)
	{
		cacheType::const_iterator it;
		if ((it = cache.find(obj))!= cache.end())
			return it->second;

		if (Aig_IsComplement(obj))
			return nf->CreateNode(NOT, convert(mgr,Aig_Regular(obj),cache));
		else if (Aig_ObjIsAnd(obj))
			{
			    ASTNode result = nf->CreateNode(AND,convert(mgr,Aig_ObjChild0(obj),cache),convert(mgr,Aig_ObjChild1(obj),cache));
				cache.insert(make_pair(obj,result));
				return result;
			}
		else if (obj == Aig_ManConst1(mgr.aigMgr))
			return bm->ASTTrue;
		else if (obj == Aig_ManConst0(mgr.aigMgr))
			return bm->ASTFalse;
		else if (Aig_ObjIsPo(obj))
			return convert(mgr,Aig_ObjChild0(obj),cache);
		else
			FatalError("Unknown type");
	}
public:

	ASTNode topLevel(const ASTNode& top)
	{
		if (top.isConstant())
			return top;

		bm->GetRunTimes()->start(RunTimes::AIGSimplifyCore);

		ASTNodeMap fromTo;

		// Replace theory nodes with new variables.
		ASTNode replaced = theoryToFresh(top,fromTo);

		Simplifier simplifier(bm);
		BBNodeManagerAIG mgr;
    	BitBlaster<BBNodeAIG, BBNodeManagerAIG> bb(&mgr, &simplifier, bm->defaultNodeFactory,&bm->UserFlags);
    	BBNodeAIG blasted = bb.BBForm(replaced);

    	Aig_ObjCreatePo(mgr.aigMgr, blasted.n);
   		Aig_ManCleanup( mgr.aigMgr); // remove nodes not connected to the PO.
    	Aig_ManCheck( mgr.aigMgr); // check that AIG looks ok.

    	assert(Aig_ManPoNum(mgr.aigMgr) == 1);

    	int initial_nodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];
   		//cerr << "Nodes before AIG rewrite:" << initial_nodeCount << endl;

		Dar_LibStart();  // About 150M instructions. Very expensive.
		Aig_Man_t * pTemp;
		Dar_RwrPar_t Pars, *pPars = &Pars;
		Dar_ManDefaultRwrParams(pPars);

		// Assertion errors occur with this enabled.
		pPars->fUseZeros = 1;

		const int iterations = 3;

		int lastNodeCount = initial_nodeCount;
		for (int i = 0; i < iterations; i++) {
			mgr.aigMgr = Aig_ManDup(pTemp = mgr.aigMgr, 0);
			Aig_ManStop(pTemp);
			Dar_ManRewrite(mgr.aigMgr, pPars);

			mgr.aigMgr = Aig_ManDup(pTemp = mgr.aigMgr, 0);
			Aig_ManStop(pTemp);

				//cerr << "After rewrite [" << i << "]  nodes:"
				//		<< mgr.aigMgr->nObjs[AIG_OBJ_AND] << endl;

			if (lastNodeCount == mgr.aigMgr->nObjs[AIG_OBJ_AND])
				break;
			lastNodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];
		}


		cacheType ptrToOrig;
    	// This needs to be done after bitblasting because the PI nodes will be altered.

    	for (BBNodeManagerAIG::SymbolToBBNode::iterator it = mgr.symbolToBBNode.begin(); it!= mgr.symbolToBBNode.end();it++)
		{
			ASTNode fresh = it->first; // the fresh variable.
			assert(fresh.GetKind() == SYMBOL);

			ASTNode result;
			if (varToNodeMap.find(fresh)== varToNodeMap.end())
				result = it->first; // It's not a fresh variable. i.e. it's a propositional var. in the original formula.
			else
				result = varToNodeMap.find(fresh)->second; // what it replaced.
			assert((it->second).size() == 1); // should be a propositional variable.
			const int index = (it->second)[0].symbol_index; // This is the index of the pi.
			Aig_Obj_t * pi = Aig_ManPi(mgr.aigMgr,index);
			ptrToOrig.insert(make_pair(pi,result));
		}

		Aig_Obj_t * pObj = (Aig_Obj_t*)Vec_PtrEntry(mgr.aigMgr->vPos, 0);

		ASTNode result = convert(mgr, pObj,ptrToOrig);

		Dar_LibStop();

		bm->GetRunTimes()->stop(RunTimes::AIGSimplifyCore);
		return result;
		//return simplifier.SimplifyFormula(result,false,NULL);
	}

};
};
#endif /* AIGSIMPLIFYPROPOSITIONALCORE_H_ */
