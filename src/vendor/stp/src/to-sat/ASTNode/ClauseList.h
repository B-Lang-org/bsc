#ifndef CLAUSELIST_H_
#define CLAUSELIST_H_

#include "../../AST/AST.h"
#include <cassert>

namespace BEEV
{

typedef vector<const ASTNode*>* ClausePtr;
typedef vector<const ASTNode*> ClauseNoPtr;
typedef deque<ClausePtr> ClauseContainer;

static bool vectorsizesort(const ClausePtr& a, const ClausePtr& b)
{
	return a->size() < b->size();
}

class ClauseList
  {
	ClauseContainer cont;
	// No copy constructor or assignment.
	ClauseList&  operator = (const ClauseList& other);
	ClauseList(const ClauseList& other);

  public:

	void appendToAllClauses(const ASTNode* n);
	void INPLACE_PRODUCT(const ClauseList& varphi2);

	ClauseContainer* asList() {
		return &cont;
	}

	bool isUnit() const
	{
		return size() ==1 && cont[0]->size() ==1;
	}

	int size() const {
		return cont.size();
	}

	ClauseList()
	{
	}

	void sort()
	{
		std::sort (cont.begin(), cont.end(), vectorsizesort);
	}

	//Putting: cont.reserve(l->size() + cont.size());
	// in here is a terrible idea.
	// reserve() will increase the size of the vector to the amount reserved.
	// If you are adding 10 clauselists of size 2, then it will increase
	// the base container by 2, 10 times.
	// However if you use the default growth strategy, it will grow in chunks,
	// perhaps doubling the backing arrays size. Requiring fewer memmoves.
	void insert(ClauseList* l) {
		cont.insert(cont.end(), l->cont.begin(), l->cont.end());
	}

	void insertAtFront(ClauseList* l) {
			cont.insert(cont.begin(), l->cont.begin(), l->cont.end());
		}

	// This deletes all the clausePtrs this container points to.
	// This isn't part of the destructor because for instance, in
	// INPLACE_UNION, the clausePtrs are already pointed to by
	// another ClauseContainer.
	void deleteJustVectors() {
		ClauseContainer::const_iterator it = cont.begin();
		for (; it != cont.end(); it++) {
			delete *it;
		}
		cont.clear();
	}

	void push_back(ClausePtr p) {
		cont.push_back(p);
	}

	void reserve(int v) {
		//cont.reserve(v);
	}

	static ClauseList* UNION(const ClauseList& varphi1, const ClauseList& varphi2)
    {
      ClauseList* psi1 = ClauseList::COPY(varphi1);
      ClauseList* psi2 = ClauseList::COPY(varphi2);
      if (psi1->size() < psi2->size())
      {
    	  psi2->insert(psi1);
    	  delete psi1;
    	  return psi2;
      }
      else
      {
    	   psi1->insert(psi2);
    	   delete psi2;
    	   return psi1;
      }
    }

    static void INPLACE_UNION(ClauseList* varphi1, const ClauseList& varphi2)
    {
      ClauseList* psi2 = ClauseList::COPY(varphi2);
      varphi1->insert( psi2);
      delete psi2;
    }

    static void NOCOPY_INPLACE_UNION(ClauseList* varphi1, ClauseList* varphi2)
    {
      varphi1->insert(varphi2);
      delete varphi2;
    }

	static ClauseList* PRODUCT(const ClauseList& varphi1,
			const ClauseList& varphi2) {

		ClauseList* psi = new ClauseList();
		psi->reserve(varphi1.size() * varphi2.size());

		ClauseContainer::const_iterator it1 = varphi1.cont.begin();
		for (; it1 != varphi1.cont.end(); it1++) {
			const ClausePtr& clause1 = *it1;
			ClauseContainer::const_iterator it2 = varphi2.cont.begin();
			for (; it2 != varphi2.cont.end(); it2++) {
				const ClausePtr& clause2 = *it2;
				ClausePtr clause = new ClauseNoPtr();
				clause->reserve(clause1->size() + clause2->size());
				clause->insert(clause->end(), clause1->begin(), clause1->end());
				clause->insert(clause->end(), clause2->begin(), clause2->end());
				psi->push_back(clause);
			}
		}
		return psi;
	}

	static ClauseList* COPY(const ClauseList& varphi) {

		ClauseList* psi = new ClauseList();
		psi->reserve(varphi.size());

		ClauseContainer::const_iterator it = varphi.cont.begin();
		for (; it != varphi.cont.end(); it++) {
			psi->push_back(new ClauseNoPtr(**it));
		}

		return psi;
	}
  };
}
#endif /* CLAUSELIST_H_ */
