/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-

#include "printers.h"

/*
 * Outputs in DOT graph format. Can be layed out by the dotty/neato tools.
 */

namespace printer
{

  using std::string;
  using namespace BEEV;

  void outputBitVec(const ASTNode n, ostream& os);

  void Dot_Print1(ostream &os, const ASTNode n, HASHSET<int> *alreadyOutput)
  {

    // check if this node has already been printed. If so return.
    if (alreadyOutput->find(n.GetNodeNum()) != alreadyOutput->end())
      return;

    alreadyOutput->insert(n.GetNodeNum());

    os << "n" << n.GetNodeNum() << "[label =\"";
    switch (n.GetKind())
      {
      case SYMBOL:
        n.nodeprint(os);
        break;

      case BITVECTOR:
      case BVCONST:
        outputBitVec(n, os);
        break;

      default:
        os << _kind_names[n.GetKind()];
      }

    os << "\"];" << endl;

    // print the edges to each child.
    ASTVec ch = n.GetChildren();
    ASTVec::iterator itend = ch.end();
    int i = 0;
    for (ASTVec::iterator it = ch.begin(); it < itend; it++)
      {
        os << "n" << n.GetNodeNum() 
           << " -> " << "n" 
           << it->GetNodeNum() 
           << "[label=" << i++ 
           << "];" << endl;
      }

    // print each of the children.
    for (ASTVec::iterator it = ch.begin(); it < itend; it++)
      {
        Dot_Print1(os, *it, alreadyOutput);
      }
  }

  ostream& Dot_Print(ostream &os, const ASTNode n)
  {

    os << "digraph G{" << endl;

    // create hashmap to hold integers (node numbers).
    HASHSET<int> alreadyOutput;

    Dot_Print1(os, n, &alreadyOutput);

    os << "}" << endl;

    return os;
  }

}
