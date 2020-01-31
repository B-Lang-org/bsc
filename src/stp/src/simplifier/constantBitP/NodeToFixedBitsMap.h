/*
 * pimpl class to make compiling easier.
 */

#ifndef NODETOFIXEDBITSMAP_H_
#define NODETOFIXEDBITSMAP_H_

#include "../../AST/AST.h"
#include "FixedBits.h"

namespace simplifier
{
  namespace constantBitP
  {

    class NodeToFixedBitsMap
    {
    public:
      typedef BEEV::hash_map<BEEV::ASTNode, FixedBits*,
          BEEV::ASTNode::ASTNodeHasher, BEEV::ASTNode::ASTNodeEqual>
          NodeToFixedBitsMapType;

      NodeToFixedBitsMapType* map;

      NodeToFixedBitsMap(int size)
      {
        map = new NodeToFixedBitsMapType(size);
      }
      virtual
      ~NodeToFixedBitsMap()
      {
        clear();
        delete map;
      }

      void
      clear()
      {
        NodeToFixedBitsMap::NodeToFixedBitsMapType::iterator itD = map->begin();
        for (; itD != map->end(); itD++)
          delete itD->second;
        map->clear();
      }
    };
  }
  ;
}
;

#endif /* NODETOFIXEDBITSMAP_H_ */
