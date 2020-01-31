#ifndef SYMBOLS_H
#define SYMBOLS_H

#include "../boost/noncopyable.hpp"

// Each node is either: empty, an ASTNode, or a vector of more than one child nodes.

class Symbols : boost::noncopyable
{
	public:

		const ASTNode found;
		const vector<Symbols*> children;

		Symbols() {
		}

		Symbols(const ASTNode& n): found(n)
		{
			assert(BEEV::SYMBOL == n.GetKind());
		}

		// This will create an "empty" node if the array is empty.
		Symbols(const vector<Symbols*>& s):
			children(s.begin(), s.end())
		{
			// Children should never be empty. They shouldn't be children.
			for(vector<Symbols*>::const_iterator it = children.begin(); it!= children.end(); it++)
			{
				assert(!(*it)->empty());
			}

			assert(children.size() != 1);
		}

		bool isLeaf()
		{
			return !found.IsNull();
		}

		bool empty() const {
			return (found.IsNull() && children.size() == 0);
		}
	};

class SymbolPtrHasher
{
public:
  size_t operator()(const Symbols * n) const
  {
    return (size_t) n;
  }
  ;
}; //End of ASTNodeHasher


#endif
