#include "ClauseList.h"
#include "../../AST/AST.h"

namespace BEEV
{

// inplace PRODUCT of "this".
void ClauseList::appendToAllClauses(const ASTNode* n) {
	ClauseContainer::iterator it1 = cont.begin();
	for (; it1 != cont.end(); it1++)
		(*it1)->push_back(n);
}

// expects varphi2 to be just a single clause.
void ClauseList::INPLACE_PRODUCT(const ClauseList& varphi2) {
	assert(1 == varphi2.size());
	ClauseList& varphi1 = *this;

	ClauseContainer::iterator it1 = varphi1.cont.begin();
	ClauseContainer::iterator this_end = varphi1.cont.end();
	const ClauseNoPtr::const_iterator& insert_end =
			varphi2.cont.front()->end();
	const ClauseNoPtr::const_iterator& insert_begin =
			varphi2.cont.front()->begin();

	for (; it1 != this_end; it1++) {
		ClausePtr p = *it1;
		p->insert(p->end(), insert_begin, insert_end);
	}
}


}
