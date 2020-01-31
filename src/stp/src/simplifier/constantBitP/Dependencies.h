#ifndef DEPENDENCIES_H_
#define DEPENDENCIES_H_

#include "../../AST/AST.h"
namespace simplifier
{
  namespace constantBitP
  {

    using namespace BEEV;

    // From a child, get the parents of that node.
    class Dependencies
    {
    private:

      typedef hash_map<BEEV::ASTNode, set<BEEV::ASTNode>*, BEEV::ASTNode::ASTNodeHasher, BEEV::ASTNode::ASTNodeEqual>
          NodeToDependentNodeMap;
      NodeToDependentNodeMap dependents;

      const set<ASTNode> empty;

    public:
      // All the nodes that depend on the value of a particular node.
      void
      build(const ASTNode & current, const ASTNode & prior)
      {
        if (current.isConstant()) // don't care about what depends on constants.
          return;

        set<ASTNode> * vec;
        const NodeToDependentNodeMap::iterator it = dependents.find(current);
        if (dependents.end() == it)
          {
            // add it in with a reference to the vector.
            vec = new set<ASTNode> ();

            dependents.insert(std::pair<ASTNode, set<ASTNode>*>(current, vec));
          }
        else
          {
            vec = it->second;
          }

        if (prior != current) // initially called with both the same.
          {
            if (vec->count(prior) == 0)
              vec->insert(prior);
            else
              return; // already been added in.
          }

        for (unsigned int i = 0; i < current.GetChildren().size(); i++)
          {
            build(current.GetChildren()[i], current);
          }
      }

      Dependencies(const Dependencies&); // Shouldn't needed to copy or assign.
      Dependencies& operator=(const Dependencies&);

    public:
      Dependencies(const ASTNode &top)
      {
        build(top, top);
        checkInvariant();
      }

      ~Dependencies()
      {
        NodeToDependentNodeMap::iterator it = dependents.begin();
        for (/**/; it != dependents.end(); it++)
          {
            //set<BEEV::ASTNode>*
            delete it->second;
          }
      }

      void replaceFresh(const ASTNode& old, const ASTNode& newN, set<ASTNode> *newNDepends,
                        ASTVec& variables)
      {
        NodeToDependentNodeMap::const_iterator it = dependents.find(old);
        if (it == dependents.end())
          return;

        it->second->erase(old);
        dependents.insert(make_pair(newN,newNDepends));
        variables.push_back(newN);
      }

      // The "toRemove" node is being removed. Used by unconstrained elimination.
      void removeNode(const ASTNode& toRemove, ASTVec& variables)
      {
        for (unsigned i = 0; i < toRemove.GetChildren().size(); i++)
          {
            const ASTNode child = toRemove.GetChildren()[i];

            NodeToDependentNodeMap::const_iterator it = dependents.find(child);
            if (it == dependents.end())
              continue;

            it->second->erase(toRemove);
            if (it->second->size() == 0)
              {
                removeNode(child,variables);
                continue;
              }

            if (child.GetKind() == SYMBOL && it->second->size() ==1)
              {
                variables.push_back(child);
              }
          }
      }

      void
      print() const
      {
        NodeToDependentNodeMap::const_iterator it = dependents.begin();
        for (/**/; it != dependents.end(); it++)
          {
            cout << (it->first).GetNodeNum();

            const set<ASTNode>* dep = it->second;

            set<ASTNode>::iterator it = dep->begin();
            while (it != dep->end())
              {
                cout << " " << (*it).GetNodeNum();
                it++;
              }
            cout << endl;
          }
      }

      void
      checkInvariant() const
      {
        // only one node with a single dependent.
      }

      const set<ASTNode>*
      getDependents(const ASTNode n) const
      {
        if (n.isConstant())
          return &empty;
        const NodeToDependentNodeMap::const_iterator it = dependents.find(n);
        if (it == dependents.end())
          return &empty;

        return it->second;
      }

      // The higher node depends on the lower node.
      // The value produces by the lower node is read by the higher node.
      bool
      nodeDependsOn(const ASTNode& higher, const ASTNode& lower) const
      {
        const set<ASTNode> *s = getDependents(lower);
        return s->count(higher) > 0;
      }

      bool isUnconstrained(const ASTNode& n)
      {
        if (n.GetKind() != SYMBOL)
          return false;

        NodeToDependentNodeMap::const_iterator it = dependents.find(n);
        assert(it != dependents.end());
        return it->second->size() ==1;
      }

#if 0
      void
      getAllVariables(ASTVec& v)
      {
        for (NodeToDependentNodeMap::const_iterator it = dependents.begin(); it != dependents. end(); it++)
          {
            if (it->first.GetKind() == SYMBOL)
              v.push_back(it->first);
          }
      }
#endif

    };

  }
  ;
}
;

#endif /* DEPENDENCIES_H_ */
