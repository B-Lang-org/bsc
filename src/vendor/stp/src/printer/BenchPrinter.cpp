#include "printers.h"
#include <string>
#include "../AST/ASTKind.h"
#include <deque>

/*
 * Bench format  which the ABC logic synthesis tool can read.
 * No more than 2-arity seem to be accepted.
 */

namespace printer
{
using std::string;
using namespace BEEV;

string name(const Kind k)
{
	return _kind_names[k];
}

string bvconstToString(const ASTNode& n)
{
	assert (n.GetKind() == BVCONST);
	std::stringstream output;
	output << *n.GetBVConst();
	return output.str();
}

// ABC doesn't like spaces, nor brackets. in variable names.
//  TODO CHECK that this doesn't cause duplicate names
string symbolToString(const ASTNode &n)
{
	assert(n.GetKind() == SYMBOL);
	std::stringstream output;
	n.nodeprint(output);

	string result = output.str();
	replace(result.begin(), result.end(), ' ', '_');
	replace(result.begin(), result.end(), '(', '_');
	replace(result.begin(), result.end(), ')', '_');

	return result;

}

string Bench_Print1(ostream &os, const ASTNode& n,
		map<ASTNode, string> *alreadyOutput)
{

	assert(((n.GetKind() == SYMBOL) || (n.GetKind() == BVCONST) || n.GetValueWidth() <= 1));
	assert(!n.IsNull());

	map<ASTNode, string>::iterator it;
	if ((it = alreadyOutput->find(n)) != alreadyOutput->end())
		return it->second;

	if (n.GetKind() == BVCONST)
	{
		(*alreadyOutput)[n] = bvconstToString(n);
		return (*alreadyOutput)[n];
	}

	if (n.GetKind() == SYMBOL)
	{
		(*alreadyOutput)[n] = symbolToString(n);
		return (*alreadyOutput)[n];
	}

	if (n.GetKind() == TRUE)
		{
		return "vdd";
		}

	if (n.GetKind() == FALSE)
		{
		return "gnd";
		}

	if (n.GetKind() == BVGETBIT)
	{
		assert(n[1].GetKind() == BVCONST);
		std::stringstream nn;
		nn << Bench_Print1(os, n[0], alreadyOutput) << "_" << Bench_Print1(os, n[1], alreadyOutput);
		(*alreadyOutput)[n] = nn.str();
		return (*alreadyOutput)[n];
	}

	std::stringstream nodeNameSS;
	nodeNameSS << "n" << n.GetNodeNum();

	string thisNode = nodeNameSS.str();
	(*alreadyOutput)[n] = thisNode;

	assert(n.Degree() > 0);
	std::stringstream output;

	// The bench format doesn't accept propositional ITEs.
	if (n.GetKind() == ITE)
	{
		assert(n.Degree() == 3);
		string p = Bench_Print1(os, n[0], alreadyOutput);
		string p1 = Bench_Print1(os, n[1], alreadyOutput);
		string p2 = Bench_Print1(os, n[2], alreadyOutput);

		os << thisNode << "_1 = AND(" << p << "," << p1 << ")" << endl;
		os << thisNode << "_2" << " = NOT(" << p << ")," << endl;
		os << thisNode << "_3" << " = AND(" << thisNode << "_2"
				<< "," << p2 << ")" << endl;
		os << thisNode << "=" << "OR(," << thisNode << "_1" << ","
				<< thisNode << "_3)" << endl;
	}
	else
	{
		if (n.Degree() > 2)
		{
			assert(n.GetKind() == AND || n.GetKind() == XOR || n.GetKind() == OR); // must be associative.
			deque<string> names;

			for (unsigned i = 0; i < n.Degree(); i++)
				names.push_back(Bench_Print1(os, n[i], alreadyOutput));

			int id = 0;

			while (names.size() > 2)
			{
				string a = names.front();
				names.pop_front();

				string b = names.front();
				names.pop_front();

				std::stringstream thisName;
				thisName << thisNode << "___" << id++;

				output << thisName.str() << "=" << name(n.GetKind()) << "("
						<< a << "," << b << ")" << endl;

				names.push_back(thisName.str());
			}

			assert(names.size() == 2);
			// last two now.

			string a = names.front();
			names.pop_front();
			string b = names.front();
			names.pop_front();

			output << thisNode << "=" << name(n.GetKind()) << "(" << a
					<< "," << b << ")" << endl;
			os << output.str();
		}
		else
		{
			output << thisNode << "=" << name(n.GetKind()) << "(";
			for (unsigned i = 0; i < n.Degree(); i++)
			{
				if (i >= 1)
					output << " , ";
				output << Bench_Print1(os, n[i], alreadyOutput);

			}
			os << output.str() << ")" << endl;
		}
	}
	return thisNode;
}

void OutputInputs(ostream &os, const ASTNode& n, hash_set<int> *alreadyOutput)
{
	if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
		return;

	alreadyOutput->insert(n.GetNodeNum());

	if (n.GetKind() == BVGETBIT)
	{
		assert(n[1].GetKind() == BVCONST);
		std::stringstream nn;
		n[0].nodeprint(nn);
		nn << "_" << bvconstToString(n[1]);
		os << "INPUT(" << nn.str() << ")" << endl;
		return;
	}

	// A boolean symbol.
	if (n.GetKind() == SYMBOL)
	{
		os << "INPUT(" << symbolToString(n) << ")" << endl;
		return;
	}

	for (unsigned i = 0; i < n.Degree(); i++)
	{
		OutputInputs(os, n[i], alreadyOutput);
	}
}

ostream& Bench_Print(ostream &os, const ASTNode n)
{
	hash_set<int> alreadyOutput2;

	OutputInputs(os, n, &alreadyOutput2);

	map<ASTNode, string> alreadyOutput;

	os << "OUTPUT(" << "n" << n.GetNodeNum() << ")" << endl;
	Bench_Print1(os, n, &alreadyOutput);
	return os;
}
}
;
