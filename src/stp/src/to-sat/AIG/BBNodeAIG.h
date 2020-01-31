// -*- c++ -*-
/********************************************************************
 * AUTHORS: Trevor Hansen
 *
 * BEGIN DATE: June, 2010
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef BBNODEAIG_H_
#define BBNODEAIG_H_

#include "../../extlib-abc/aig.h"
#include <iostream>

namespace BEEV
{
  using std::cerr;
  using std::endl;

  // This class wraps around a pointer to an AIG (provided by the ABC tool).
  // uses the default copy constructor and assignment operator.

  class BBNodeAIG
{
  // This is only useful for printing small instances for debuging.
    void print(Aig_Obj_t* node) const
    {
      Aig_Obj_t *c0 = node->pFanin0, *c1 = node->pFanin1;
      bool c0Not = Aig_IsComplement(c0), c1Not = Aig_IsComplement(c1);
      if (c0Not)
        c0 = Aig_Not(c0);
      if (c1Not)
        c1 = Aig_Not(c1);

      cerr << node->Id;
      cerr << "[" << node->Type << "]";
      cerr << ": (";
      if (c0 !=0 )
        {
            if (c0Not)
               cerr << "-";
            cerr << c0->Id;
            cerr <<",";
        }
      if (c1 !=0 )
        {
        if (c1Not)
           cerr << "-";

        cerr << c1->Id;
        }
      cerr << ")" << endl;
      if (c0 !=0 )
        print(c0);
      if (c1 !=0 )
        print(c1);
    }
public:

    intptr_t GetNodeNum() const
        {
          return (intptr_t)n;
        }

    // If the pointer is odd. Then it's the NOT of the pointer one less.
	Aig_Obj_t * n;

	// After dag aware rewriting the symbol stays at the same position in the vector of PIs.
	// To get it's CNF variable number we get the node at the same position.
	int symbol_index;

	BBNodeAIG()
	{
		n = NULL;
	}

	BBNodeAIG(Aig_Obj_t * _n)
	{
		n = _n;
            assert(n!=NULL);
            if (Aig_IsComplement(n))
              {
              assert(Aig_Not(n)->Type != 0); // don't want nodes of type UNKNOWN>
	}
            else
              {
              assert(n->Type!=0);
              }
	}

	bool IsNull() const
	{
		return n == NULL;
	}

	bool operator==(const BBNodeAIG &other) const
	{
	  return n == other.n;
	}

	bool operator!=(const BBNodeAIG &other) const
	{
		return !(n == other.n);
	}


	bool operator<(const BBNodeAIG &other) const
	{
		return n < other.n;
	}

	void print() const
	{
          print(n);
	}

};
}
;

#endif
