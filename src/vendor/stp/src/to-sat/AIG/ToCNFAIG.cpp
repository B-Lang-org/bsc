#include "ToCNFAIG.h"


namespace BEEV
{

// Can it only add in the new variables somehow??
void addVariables(BBNodeManagerAIG& mgr, Cnf_Dat_t*& cnfData , ToSATBase::ASTNodeToSATVar& nodeToVar)
{
	BBNodeManagerAIG::SymbolToBBNode::const_iterator it;
	// Each symbol maps to a vector of CNF variables.
	for (it = mgr.symbolToBBNode.begin(); it != mgr.symbolToBBNode.end(); it++) {
		const ASTNode& n = it->first;
		const vector<BBNodeAIG> &b = it->second;

		const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();

		// INT_MAX for parts of symbols that didn't get encoded.
		vector<unsigned> v(width, ~((unsigned) 0));

		for (unsigned i = 0; i < b.size(); i++) {
			if (!b[i].IsNull()) {
				Aig_Obj_t * pObj;
				pObj = (Aig_Obj_t*) Vec_PtrEntry(mgr.aigMgr->vPis,
						b[i].symbol_index);
				v[i] = cnfData->pVarNums[pObj->Id];
			}
		}
		nodeToVar.insert(make_pair(n, v));
	}
}

void ToCNFAIG::toCNF(const BBNodeAIG& top, Cnf_Dat_t*& cnfData,
		ToSATBase::ASTNodeToSATVar& nodeToVar,
		bool needAbsRef, BBNodeManagerAIG& mgr) {
	assert(cnfData == NULL);

	Aig_ObjCreatePo(mgr.aigMgr, top.n);
	if (!needAbsRef) {
		Aig_ManCleanup( mgr.aigMgr); // remove nodes not connected to the PO.
	}
	Aig_ManCheck( mgr.aigMgr); // check that AIG looks ok.

	assert(Aig_ManPoNum(mgr.aigMgr) == 1);

	// UseZeroes gives assertion errors.
	// Rewriting is sometimes very slow. Can it be configured to be faster?
	// What about refactoring???

	int nodeCount = mgr.aigMgr->nObjs[AIG_OBJ_AND];
	if (uf.stats_flag)
		cerr << "Nodes before AIG rewrite:" << nodeCount << endl;

	if (!needAbsRef && uf.isSet("aig-rewrite","0")) {
		Dar_LibStart();
		Aig_Man_t * pTemp;
		Dar_RwrPar_t Pars, *pPars = &Pars;
		Dar_ManDefaultRwrParams(pPars);

		// Assertion errors occur with this enabled.
		// pPars->fUseZeros = 1;

		// For mul63bit.smt2 with iterations =3 & nCutsMax = 8
		// CNF generation was taking 139 seconds, solving 10 seconds.

		// With nCutsMax =2, CNF generation takes 16 seconds, solving 10 seconds.
		// The rewriting doesn't remove as many nodes of course..
		int iterations = 3;

		for (int i = 0; i < iterations; i++) {
			mgr.aigMgr = Aig_ManDup(pTemp = mgr.aigMgr, 0);
			Aig_ManStop(pTemp);
			Dar_ManRewrite(mgr.aigMgr, pPars);

			mgr.aigMgr = Aig_ManDup(pTemp = mgr.aigMgr, 0);
			Aig_ManStop(pTemp);

			if (uf.stats_flag)
				cerr << "After rewrite [" << i << "]  nodes:"
						<< mgr.aigMgr->nObjs[AIG_OBJ_AND] << endl;

			if (nodeCount == mgr.aigMgr->nObjs[AIG_OBJ_AND])
				break;

		}
	}
	if (!uf.isSet("simple-cnf","0")) {
		cnfData = Cnf_Derive(mgr.aigMgr, 0);
		if (uf.stats_flag)
		  cerr << "advanced CNF" << endl;
	} else {
		cnfData = Cnf_DeriveSimple(mgr.aigMgr, 0);
                if (uf.stats_flag)
                	cerr << "simple CNF" << endl;

	}

	BBNodeManagerAIG::SymbolToBBNode::const_iterator it;

	assert(nodeToVar.size() == 0);

	//todo. cf. with addvariables above...
	// Each symbol maps to a vector of CNF variables.
	for (it = mgr.symbolToBBNode.begin(); it != mgr.symbolToBBNode.end(); it++) {
		const ASTNode& n = it->first;
		const vector<BBNodeAIG> &b = it->second;
		assert(nodeToVar.find(n) == nodeToVar.end());

		const int width = (n.GetType() == BOOLEAN_TYPE) ? 1 : n.GetValueWidth();

		// INT_MAX for parts of symbols that didn't get encoded.
		vector<unsigned> v(width, ~((unsigned) 0));

		for (unsigned i = 0; i < b.size(); i++) {
			if (!b[i].IsNull()) {
				Aig_Obj_t * pObj;
				pObj = (Aig_Obj_t*) Vec_PtrEntry(mgr.aigMgr->vPis,
						b[i].symbol_index);
				v[i] = cnfData->pVarNums[pObj->Id];
			}
		}

		nodeToVar.insert(make_pair(n, v));
	}
	assert(cnfData != NULL);
}
};
