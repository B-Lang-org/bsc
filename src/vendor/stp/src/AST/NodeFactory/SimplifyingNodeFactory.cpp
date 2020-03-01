/* A node factory that:
 * 	    * Sorts children to increases sharing,
 *	    * Performs constant evaluation,
 *	    * performs simplify boolean simplifications,
 *	    * converts less thans to greater thans.
 *
 * NOTE: CreateNode doesn't necessary return a node with the same Kind as what it was called
 * with. For example: (AND TRUE FALSE) will return FALSE. Which isn't an AND node.
 *
 * The intention is to never create nodes that will later be simplified by single level
 * re-write rules. So we will never create the node (NOT(NOT x)). This is and example of
 * a multi-level rule that never increases the global number of nodes.
 *
 * These rules (mostly) don't increase the total number of nodes by more than one.
 *
 * Sometimes the number of nodes is increased. e.g. creating BVSLT(x,y), will create NOT(BVGT(y,x)).
 * i.e. it will create an extra node.
 *
 * I think we've got all the two input cases that either map to a constant, or to an input value.
 * e.g. (a >> a), (a xor a), (a or a), (a and a), (a + 0), (a-0)..
 *
 */

#include "../../AST/AST.h"
#include <cassert>
#include "SimplifyingNodeFactory.h"
#include "../../simplifier/simplifier.h"
#include "../ArrayTransformer.h"
#include <cmath>

using BEEV::Kind;

using BEEV::SYMBOL;
using BEEV::BVNEG;
using BEEV::BVMOD;
using BEEV::BVUMINUS;
using BEEV::BVMULT;
using BEEV::ITE;
using BEEV::EQ;
using BEEV::BVSRSHIFT;
using BEEV::SBVREM;
using BEEV::SBVMOD;
using BEEV::SBVDIV;
using BEEV::BVCONCAT;
using BEEV::BVEXTRACT;
using BEEV::BVRIGHTSHIFT;
using BEEV::BVPLUS;
using BEEV::BVXOR;
using BEEV::BVDIV;

static bool debug_simplifyingNodeFactory = false;

ASTNode
SimplifyingNodeFactory::CreateNode(Kind kind, const ASTVec & children)
{

  assert(kind != SYMBOL);
  // These are created specially.

  // If all the parameters are constant, return the constant value.
  // The bitblaster calls CreateNode with a boolean vector. We don't try to simplify those.
  if (kind != BEEV::UNDEFINED && kind != BEEV::BOOLEAN && kind != BEEV::BITVECTOR && kind != BEEV::ARRAY)
    {
      bool allConstant = true;

      for (unsigned i = 0; i < children.size(); i++)
        if (!children[i].isConstant())
          {
            allConstant = false;
            break;
          }

      if (allConstant)
        {
          const ASTNode& hash = hashing.CreateNode(kind, children);
          const ASTNode& c = NonMemberBVConstEvaluator(hash);
          assert(c.isConstant());
          return c;
        }
    }
  ASTNode result;

  switch (kind)
    {
  // convert the Less thans to greater thans.
  case BEEV::BVLT:
    assert(children.size() ==2);
    result = NodeFactory::CreateNode(BEEV::BVGT, children[1], children[0]);
    break;

  case BEEV::BVLE:
    assert(children.size() ==2);
    result = NodeFactory::CreateNode(BEEV::BVGE, children[1], children[0]);
    break;

  case BEEV::BVSLT:
    assert(children.size() ==2);
    result = NodeFactory::CreateNode(BEEV::BVSGT, children[1], children[0]);
    break;

  case BEEV::BVSLE:
    assert(children.size() ==2);
    result = NodeFactory::CreateNode(BEEV::BVSGE, children[1], children[0]);
    break;

  case BEEV::BVSGT:
    assert(children.size() ==2);
    if (children[0] == children[1])
      result = ASTFalse;
    if (children[1].GetKind() == BEEV::BVCONST)
      {
        // 011111111 (most positive number.)
        unsigned width = children[0].GetValueWidth();
        BEEV::CBV max = CONSTANTBV::BitVector_Create(width, false);
        CONSTANTBV::BitVector_Fill(max);
        CONSTANTBV::BitVector_Bit_Off(max, width - 1);
        ASTNode biggestNumber = bm.CreateBVConst(max, width);
        if (children[1] == biggestNumber)
          result = ASTFalse;
      }
    if (children[0].GetKind() == BEEV::BVCONST)
      {
        unsigned width = children[0].GetValueWidth();
        // 1000000000 (most negative number.)
        BEEV::CBV max = CONSTANTBV::BitVector_Create(width, true);
        CONSTANTBV::BitVector_Bit_On(max, width - 1);
        ASTNode smallestNumber = bm.CreateBVConst(max, width);
        if (children[0] == smallestNumber)
          result = ASTFalse;
      }

    if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT && children[0][1] == children[1][1])
      result = NodeFactory::CreateNode(BEEV::BVSGT, children[0][0], children[1][0]);

    break;

  case BEEV::BVGT:
    assert(children.size() ==2);
    if (children[0] == children[1])
      result = ASTFalse;
    if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
      result = ASTFalse;
    if (children[1].isConstant() && CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
      result = ASTFalse;
    if (children[0].GetKind() == BVRIGHTSHIFT && children[0][0] == children[1])
      result = ASTFalse;
    if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT && children[0][1] == children[1][1])
      result = NodeFactory::CreateNode(BEEV::BVGT, children[0][0], children[1][0]);
    if (children[0].GetKind() == BVCONCAT && children[1].GetKind() == BVCONCAT && children[0][0] == children[1][0])
      result = NodeFactory::CreateNode(BEEV::BVGT, children[0][1], children[1][1]);
    if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
      result = NodeFactory::CreateNode(BEEV::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
    if (children[0].isConstant() && CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
      result = NodeFactory::CreateNode(BEEV::NOT, NodeFactory::CreateNode(EQ, children[0], children[1]));
    if (children[0].GetKind() == BEEV::BVAND && children[0].Degree() > 1
        && ((children[0][0] == children[1]) || children[0][1] == children[1]))
      result = ASTFalse;
    break;

  case BEEV::BVGE:
    assert(children.size() ==2);
      {
        ASTNode a = NodeFactory::CreateNode(BEEV::BVGT, children[1], children[0]);
        result = NodeFactory::CreateNode(BEEV::NOT, a);
      }
    break;

  case BEEV::BVSGE:
    assert(children.size() ==2);
      {
        ASTNode a = NodeFactory::CreateNode(BEEV::BVSGT, children[1], children[0]);
        result = NodeFactory::CreateNode(BEEV::NOT, a);
      }
    break;

  case BEEV::NOT:
    result = CreateSimpleNot(children);
    break;
  case BEEV::AND:
    result = CreateSimpleAndOr(1, children);
    break;
  case BEEV::OR:
    result = CreateSimpleAndOr(0, children);
    break;
  case BEEV::NAND:
    result = CreateSimpleNot(CreateSimpleAndOr(1, children));
    break;
  case BEEV::NOR:
    result = CreateSimpleNot(CreateSimpleAndOr(0, children));
    break;
  case BEEV::XOR:
    result = CreateSimpleXor(children);
    break;
  case ITE:
    result = CreateSimpleFormITE(children);
    break;
  case EQ:
    result = CreateSimpleEQ(children);
    break;
  case BEEV::IFF:
    {
      assert(children.size() ==2);
      ASTVec newCh;
      newCh.reserve(2);
      newCh.push_back(CreateSimpleNot(children[0]));
      newCh.push_back(children[1]);
      result = CreateSimpleXor(newCh);
      break;
    }
  case BEEV::IMPLIES:
    {
      assert(children.size() ==2);
      if (children[0] == children[1])
        result = bm.ASTTrue;
      else
        {
          ASTVec newCh;
          newCh.reserve(2);
          newCh.push_back(CreateSimpleNot(children[0]));
          newCh.push_back(children[1]);
          result = CreateSimpleAndOr(0, newCh);
        }
      break;
    }

  default:
    result = hashing.CreateNode(kind, children);
    }

  if (result.IsNull())
    result = hashing.CreateNode(kind, children);

  return result;
}

ASTNode
SimplifyingNodeFactory::CreateSimpleNot(const ASTNode& form)
{
  const Kind k = form.GetKind();
  switch (k)
    {
  case BEEV::FALSE:
    {
      return form.GetSTPMgr()->ASTTrue;
    }
  case BEEV::TRUE:
    {
      return form.GetSTPMgr()->ASTFalse;
    }
  case BEEV::NOT:
    {
      return form[0];
    } // NOT NOT cancellation
  default:
    {
      ASTVec children;
      children.push_back(form);
      return hashing.CreateNode(BEEV::NOT, children);
    }
    }
}

ASTNode
SimplifyingNodeFactory::CreateSimpleNot(const ASTVec& children)
{
  const Kind k = children[0].GetKind();
  switch (k)
    {
  case BEEV::FALSE:
    {
      return children[0].GetSTPMgr()->ASTTrue;
    }
  case BEEV::TRUE:
    {
      return children[0].GetSTPMgr()->ASTFalse;
    }
  case BEEV::NOT:
    {
      return children[0][0];
    } // NOT NOT cancellation
  default:
    {
      return hashing.CreateNode(BEEV::NOT, children);
    }
    }
}

ASTNode
SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd, const ASTNode& form1, const ASTNode& form2)
{
  ASTVec children;
  children.push_back(form1);
  children.push_back(form2);
  return CreateSimpleAndOr(IsAnd, children);
}

ASTNode
SimplifyingNodeFactory::CreateSimpleAndOr(bool IsAnd, const ASTVec &children)
{
  const Kind k = IsAnd ? BEEV::AND : BEEV::OR;

  if (k == BEEV::OR && children.size() == 2)
    {
      const ASTNode& c0 = children[0];
      const ASTNode& c1 = children[1];
      if (c0.GetKind() == BEEV::NOT && c0[0] == c1)
        return ASTTrue;
      if (c1.GetKind() == BEEV::NOT && c1[0] == c0)
        return ASTTrue;
    }
  if (k == BEEV::AND && children.size() == 2)
    {
      const ASTNode& c0 = children[0];
      const ASTNode& c1 = children[1];
      if (c0.GetKind() == BEEV::NOT && c0[0] == c1)
        return ASTFalse;
      if (c1.GetKind() == BEEV::NOT && c1[0] == c0)
        return ASTFalse;
    }

  const ASTNode& annihilator = (IsAnd ? ASTFalse : ASTTrue);
  const ASTNode& identity = (IsAnd ? ASTTrue : ASTFalse);

  ASTNode retval;
  ASTVec new_children;
  new_children.reserve(children.size());

  const ASTVec::const_iterator it_end = children.end();
  for (ASTVec::const_iterator it = children.begin(); it != it_end; it++)
    {
      ASTVec::const_iterator next_it;

      bool nextexists = (it + 1 < it_end);
      if (nextexists)
        next_it = it + 1;
      else
        next_it = it_end;

      if (nextexists)
        if (next_it->GetKind() == BEEV::NOT && (*next_it)[0] == *it)
          return annihilator;

      if (*it == annihilator)
        {
          return annihilator;
        }
      else if (*it == identity || (nextexists && (*next_it == *it)))
        {
          // just drop it
        }
      else
        new_children.push_back(*it);
    }

  // If we get here, we saw no annihilators, and children should
  // be only the non-True nodes.

  if (0 == new_children.size())
    {
      retval = identity;
    }
  else if (1 == new_children.size())
    {
      // there is just one child
      retval = new_children[0];
    }
  else
    {
      // 2 or more children.  Create a new node.
      retval = hashing.CreateNode(IsAnd ? BEEV::AND : BEEV::OR, new_children);
    }
  return retval;
}

//Tries to simplify the input to TRUE/FALSE. if it fails, then
//return the constructed equality
ASTNode
SimplifyingNodeFactory::CreateSimpleEQ(const ASTVec& children)
{
  assert(children.size() == 2);

  // SYMBOL = something, if not that, then CONSTANT =
  const bool swap = (children[1].GetKind() == BEEV::SYMBOL
      || ((children[0].GetKind() != BEEV::SYMBOL) && children[1].GetKind() == BEEV::BVCONST));
  const ASTNode& in1 = swap ? children[1] : children[0];
  const ASTNode& in2 = swap ? children[0] : children[1];
  const Kind k1 = in1.GetKind();
  const Kind k2 = in2.GetKind();
  const int width = in1.GetValueWidth();

  if (in1 == in2)
    //terms are syntactically the same
    return in1.GetSTPMgr()->ASTTrue;

  //here the terms are definitely not syntactically equal but may be
  //semantically equal.
  if (BEEV::BVCONST == k1 && BEEV::BVCONST == k2)
    return in1.GetSTPMgr()->ASTFalse;

  if ((k1 == BVNEG && k2 == BVNEG) || (k1 == BVUMINUS && k2 == BVUMINUS))
    return NodeFactory::CreateNode(EQ, in1[0], in2[0]);

  if ((k1 == BVUMINUS && k2 == BEEV::BVCONST) || (k1 == BVNEG && k2 == BEEV::BVCONST))
    return NodeFactory::CreateNode(EQ, in1[0], NodeFactory::CreateTerm(k1, width, in2));

  if ((k2 == BVUMINUS && k1 == BEEV::BVCONST) || (k2 == BVNEG && k1 == BEEV::BVCONST))
    return NodeFactory::CreateNode(EQ, in2[0], NodeFactory::CreateTerm(k2, width, in1));

  if ((k1 == BVNEG && in1[0] == in2) || (k2 == BVNEG && in2[0] == in1))
    return in1.GetSTPMgr()->ASTFalse;

  if (k2 == BEEV::BVDIV && k1 == BEEV::BVCONST && (in1 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(BEEV::BVGT, in2[1], in2[0]);

  if (k1 == BEEV::BVDIV && k2 == BEEV::BVCONST && (in2 == bm.CreateZeroConst(width)))
    return NodeFactory::CreateNode(BEEV::BVGT, in1[1], in1[0]);

  // split the constant to equal each part of the concat.
  if (BVCONCAT == k2 && BEEV::BVCONST == k1)
    {
      int low_b = 0;
      int high_b = in2[1].GetValueWidth() - 1;
      int low_t = in2[1].GetValueWidth();
      int high_t = width - 1;

      ASTNode c0 = NodeFactory::CreateTerm(BVEXTRACT, in2[1].GetValueWidth(), in1, bm.CreateBVConst(32, high_b),
          bm.CreateBVConst(32, low_b));
      ASTNode c1 = NodeFactory::CreateTerm(BVEXTRACT, in2[0].GetValueWidth(), in1, bm.CreateBVConst(32, high_t),
          bm.CreateBVConst(32, low_t));

      ASTNode a = NodeFactory::CreateNode(EQ, in2[1], c0);
      ASTNode b = NodeFactory::CreateNode(EQ, in2[0], c1);
      return NodeFactory::CreateNode(BEEV::AND, a, b);
    }

  // This increases the number of nodes. So disable for now.
  if (false && BVCONCAT == k1 && BVCONCAT == k2 && in1[0].GetValueWidth() == in2[0].GetValueWidth())
    {
      ASTNode a = NodeFactory::CreateNode(EQ, in1[0], in2[0]);
      ASTNode b = NodeFactory::CreateNode(EQ, in1[1], in2[1]);
      return NodeFactory::CreateNode(BEEV::AND, a, b);
    }

  if (k1 == BEEV::BVCONST && k2 == ITE && in2[1].GetKind() == BEEV::BVCONST && in2[2].GetKind() == BEEV::BVCONST)
    {

      ASTNode result = NodeFactory::CreateNode(ITE, in2[0], NodeFactory::CreateNode(EQ, in1, in2[1]),
          NodeFactory::CreateNode(EQ, in1, in2[2]));

      return result;
    }

  // Don't create a PLUS with the same operand on both sides.
  // We don't do big pluses, because 1) this algorithm isn't good enough
  // 2) it might split nodes (a lot).
  if ((k1 == BVPLUS && in1.Degree() <= 2) || (k2 == BVPLUS && in2.Degree() <= 2))
    {
      const ASTVec& c1 = (k1 == BVPLUS) ? in1.GetChildren() : ASTVec(1, in1);
      const ASTVec& c2 = (k2 == BVPLUS) ? in2.GetChildren() : ASTVec(1, in2);

      if (c1.size() <= 2 && c2.size() <= 2)
        {
          int match1 = -1, match2 = -1;

          for (int i = 0; i < c1.size(); i++)
            for (int j = 0; j < c2.size(); j++)
              {
                if (c1[i] == c2[j])
                  {
                    match1 = i;
                    match2 = j;
                  }
              }

          if (match1 != -1)
            {
              assert(match2 !=-1);
              assert(match1 == 0 || match1 == 1);
              assert(match2 == 0 || match2 == 1);
              // If it was 1 element before, it's zero now.
              ASTNode n1 = c1.size() == 1 ? bm.CreateZeroConst(width) : c1[match1 == 0 ? 1 : 0];
              ASTNode n2 = c2.size() == 1 ? bm.CreateZeroConst(width) : c2[match2 == 0 ? 1 : 0];
              return NodeFactory::CreateNode(EQ, n1, n2);
            }
        }
    }

  if (k2 == BVPLUS && in2.Degree() == 2 && (in2[1] == in1 || in2[0] == in1))
    {
      return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in2[1] == in1 ? in2[0] : in2[1]);
    }

  if (k1 == BVPLUS && in1.Degree() == 2 && (in1[1] == in2 || in1[0] == in2))
    {
      return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in1[1] == in2 ? in1[0] : in1[1]);
    }

  if (k1 == BEEV::BVCONST && k2 == BEEV::BVXOR && in2.Degree() == 2 && in2[0].GetKind() == BEEV::BVCONST)
    {
      return NodeFactory::CreateNode(EQ, NodeFactory::CreateTerm(BEEV::BVXOR, width, in1, in2[0]), in2[1]);
    }

  if (k2 == BEEV::BVCONST && k1 == BEEV::BVXOR && in1.Degree() == 2 && in1[0].GetKind() == BEEV::BVCONST)
    {
      return NodeFactory::CreateNode(EQ, NodeFactory::CreateTerm(BEEV::BVXOR, width, in2, in1[0]), in1[1]);
    }

  if (k2 == BEEV::BVXOR && in2.Degree() == 2 && in1 == in2[0])
    {
      return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in2[1]);
    }

  if (k1 == BEEV::BVXOR && in1.Degree() == 2 && in2 == in1[0])
    {
      return NodeFactory::CreateNode(EQ, bm.CreateZeroConst(width), in1[1]);
    }

  if (k1 == BEEV::BVCONST && k2 == BEEV::BVSX && (in2[0].GetValueWidth() != width))
    {
      // Each of the bits in the extended part, and one into the un-extended part must be the same.
      bool foundZero = false, foundOne = false;
      const unsigned original_width = in2[0].GetValueWidth();
      const unsigned new_width = in2.GetValueWidth();
      for (int i = original_width - 1; i < new_width; i++)
        if (CONSTANTBV::BitVector_bit_test(in1.GetBVConst(), i))
          foundOne = true;
        else
          foundZero = true;
      if (foundZero && foundOne)
        return ASTFalse;
      ASTNode lhs = NodeFactory::CreateTerm(BVEXTRACT, original_width, in1, bm.CreateBVConst(32, original_width - 1),
          bm.CreateZeroConst(32));
      ASTNode rhs = NodeFactory::CreateTerm(BVEXTRACT, original_width, in2, bm.CreateBVConst(32, original_width - 1),
          bm.CreateZeroConst(32));
      return NodeFactory::CreateNode(EQ, lhs, rhs);
    }

  // Simplifiy (5 = 4/x) to FALSE.
  if (bm.UserFlags.division_by_zero_returns_one_flag && k1 == BEEV::BVCONST && k2 == BEEV::BVDIV
      && in2[0].GetKind() == BEEV::BVCONST)
    {
      ASTNode oneV = bm.CreateOneConst(width);
      if (CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(), oneV.GetBVConst()) > 0 && in1 != oneV
          && CONSTANTBV::BitVector_Lexicompare(in1.GetBVConst(), in2[0].GetBVConst()) > 0)
        {
          return ASTFalse;
        }
    }

  if (k1 == BVNEG && k2 == BVUMINUS && in1[0] == in2[0])
    return ASTFalse;

  if (k1 == BVUMINUS && k2 == BVNEG && in1[0] == in2[0])
    return ASTFalse;

  //last resort is to CreateNode
  return hashing.CreateNode(EQ, children);
}

// Constant children are accumulated in "accumconst".
ASTNode
SimplifyingNodeFactory::CreateSimpleXor(const ASTVec &children)
{
  if (debug_simplifyingNodeFactory)
    {
      cout << "========" << endl << "CreateSimpXor ";
      lpvec(children);
      cout << endl;
    }

  ASTVec flat_children; // empty vector
  flat_children = children;

  // sort so that identical nodes occur in sequential runs, followed by
  // their negations.
  SortByExprNum(flat_children);

  // This is the C Boolean value of all constant args seen.  It is initially
  // 0.  TRUE children cause it to change value.
  bool accumconst = 0;

  ASTVec new_children;
  new_children.reserve(children.size());

  const ASTVec::const_iterator it_end = flat_children.end();
  ASTVec::iterator next_it;
  for (ASTVec::iterator it = flat_children.begin(); it != it_end; it++)
    {
      next_it = it + 1;
      bool nextexists = (next_it < it_end);

      if (ASTTrue == *it)
        {
          accumconst = !accumconst;
        }
      else if (ASTFalse == *it)
        {
          // Ignore it
        }
      else if (nextexists && (*next_it == *it))
        {
          // x XOR x = FALSE.  Skip current, write "false" into next_it
          // so that it gets tossed, too.
          *next_it = ASTFalse;
        }
      else if (nextexists && (next_it->GetKind() == BEEV::NOT) && ((*next_it)[0] == *it))
        {
          // x XOR NOT x = TRUE.  Skip current, write "true" into next_it
          // so that it gets tossed, too.
          *next_it = ASTTrue;
        }
      else if (BEEV::NOT == it->GetKind())
        {
          // If child is (NOT alpha), we can flip accumconst and use alpha.
          // This is ok because (NOT alpha) == TRUE XOR alpha
          accumconst = !accumconst;
          // CreateSimpNot just takes child of not.
          new_children.push_back(CreateSimpleNot(*it));
        }
      else
        {
          new_children.push_back(*it);
        }
    }

  ASTNode retval;

  // Children should be non-constant.
  if (new_children.size() < 2)
    {
      if (0 == new_children.size())
        {
          // XOR(TRUE, FALSE) -- accumconst will be 1.
          if (accumconst)
            {
              retval = ASTTrue;
            }
          else
            {
              retval = ASTFalse;
            }
        }
      else
        {
          // there is just one child
          // XOR(x, TRUE) -- accumconst will be 1.
          if (accumconst)
            {
              retval = CreateSimpleNot(new_children[0]);
            }
          else
            {
              retval = new_children[0];
            }
        }
    }
  else
    {
      // negate first child if accumconst == 1
      if (accumconst)
        {
          new_children[0] = CreateSimpleNot(new_children[0]);
        }
      retval = hashing.CreateNode(BEEV::XOR, new_children);
    }

  if (debug_simplifyingNodeFactory)
    {
      cout << "returns " << retval << endl;
    }
  return retval;
}

ASTNode
SimplifyingNodeFactory::CreateSimpleFormITE(const ASTVec& children)
{
  const ASTNode& child0 = children[0];
  const ASTNode& child1 = children[1];
  const ASTNode& child2 = children[2];

  ASTNode retval;

  if (debug_simplifyingNodeFactory)
    {
      cout << "========" << endl << "CreateSimpleFormITE " << child0 << child1 << child2 << endl;
    }

  if (ASTTrue == child0)
    {
      retval = child1;
    }
  else if (ASTFalse == child0)
    {
      retval = child2;
    }
  else if (child1 == child2)
    {
      retval = child1;
    }
  // ITE(x, TRUE, y ) == x OR y
  else if (ASTTrue == child1)
    {
      retval = CreateSimpleAndOr(0, child0, child2);
    }
  // ITE(x, FALSE, y ) == (!x AND y)
  else if (ASTFalse == child1)
    {
      retval = CreateSimpleAndOr(1, CreateSimpleNot(child0), child2);
    }
  // ITE(x, y, TRUE ) == (!x OR y)
  else if (ASTTrue == child2)
    {
      retval = CreateSimpleAndOr(0, CreateSimpleNot(child0), child1);
    }
  // ITE(x, y, FALSE ) == (x AND y)
  else if (ASTFalse == child2)
    {
      retval = CreateSimpleAndOr(1, child0, child1);
    }
  else if (child0 == child1)
    {
      retval = CreateSimpleAndOr(0, child0, child2);
    }
  else if (child0 == child2)
    {
      retval = CreateSimpleAndOr(1, child0, child1);
    }
  else
    {
      retval = hashing.CreateNode(ITE, children);
    }

  if (debug_simplifyingNodeFactory)
    {
      cout << "returns " << retval << endl;
    }

  return retval;
}

// Move reads down through writes until, either we hit a write to an identical (syntactically) index,
// or we hit a write to an index that might be the same. This is intended to simplify things like:
// read(write(write(A,1,2),2,3),4) cheaply.
// The "children" that are passed should be the children of a READ.
ASTNode
SimplifyingNodeFactory::chaseRead(const ASTVec& children, unsigned int width)
{
  assert(children[0].GetKind() == BEEV::WRITE);
  const ASTNode& readIndex = children[1];
  ASTNode write = children[0];

  const bool read_is_const = (BEEV::BVCONST == readIndex.GetKind());
  ASTVec c(2);

  while (write.GetKind() == BEEV::WRITE)
    {
      const ASTNode& write_index = write[1];

      if (readIndex == write_index)
        {
          // The are definately the same.
          //cerr << "-";
          return write[2];
        }
      else if (read_is_const && BEEV::BVCONST == write_index.GetKind())
        {
          // They are definately different. Ignore this.
          //cerr << "+";
        }
      else
        {
          // They may be the same. Exit.
          // We've finished the cheap tests, now do the expensive one.
          // I don't know if the cost of this justifies the benefit.
          //cerr << "#";
          c[0] = write_index;
          c[1] = readIndex;
          ASTNode n = CreateSimpleEQ(c);
          if (n == ASTTrue)
            {
              //cerr << "#";
              return write[2];
            }
          else if (n == ASTFalse)
            {
              //cerr << "!";
            }
          else
            {
              //cerr << "."
              //Perhaps they are the same, perhaps not.
              break;
            }
        }
      write = write[0];
    }
  return hashing.CreateTerm(BEEV::READ, width, write, readIndex);
}

// This gets called with the arguments swapped as well. So the rules don't need to know about commutivity.
ASTNode
SimplifyingNodeFactory::plusRules(const ASTNode& n0, const ASTNode& n1)
{
  ASTNode result;
  const int width = n0.GetValueWidth();

  if (n0.isConstant() && CONSTANTBV::BitVector_is_empty(n0.GetBVConst()))
    result = n1;
  else if (width == 1 && n0 == n1)
    result = bm.CreateZeroConst(1);
  else if (n0 == n1)
    result = NodeFactory::CreateTerm(BEEV::BVMULT, width, bm.CreateBVConst(string("2"), 10, width), n0);
  else if (n0.GetKind() == BVUMINUS && n1 == n0[0])
    result = bm.CreateZeroConst(width);
  else if (n1.GetKind() == BVPLUS && n1[1].GetKind() == BVUMINUS && n0 == n1[1][0] && n1.Degree() == 2)
    result = n1[0];
  else if (n1.GetKind() == BVPLUS && n1[0].GetKind() == BVUMINUS && n0 == n1[0][0] && n1.Degree() == 2)
    result = n1[1];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS && n0.Degree() == 2 && n1[0] == n0[1])
    result = n0[0];
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVPLUS && n0.Degree() == 2 && n1[0] == n0[0])
    result = n0[1];
  else if (n1.GetKind() == BVNEG && n1[0] == n0)
    result = bm.CreateMaxConst(width);
  else if (n0.GetKind() == BEEV::BVCONST && n1.GetKind() == BVPLUS && n1.Degree() == 2
      && n1[0].GetKind() == BEEV::BVCONST)
    {
      ASTVec ch;
      ch.push_back(n0);
      ch.push_back(n1[0]);
      ASTNode constant = NonMemberBVConstEvaluator(&bm, BVPLUS, ch, width);
      result = NodeFactory::CreateTerm(BVPLUS, width, constant, n1[1]);
    }
  else if (n1.GetKind() == BVUMINUS && (n0.isConstant() && CONSTANTBV::BitVector_is_full(n0.GetBVConst())))
    {
      result = NodeFactory::CreateTerm(BVNEG, width, n1[0]);
    }
  else if (n1.GetKind() == BVUMINUS && n0.GetKind() == BVUMINUS)
    {
      ASTNode r = NodeFactory::CreateTerm(BVPLUS, width, n0[0], n1[0]);
      result = NodeFactory::CreateTerm(BVUMINUS, width, r);
    }

  return result;
}

ASTNode
SimplifyingNodeFactory::CreateTerm(Kind kind, unsigned int width, const ASTVec &children)
{
  if (!is_Term_kind(kind))
    FatalError("CreateTerm:  Illegal kind to CreateTerm:", ASTUndefined, kind);

  assert(kind != BEEV::BVCONST);
  // These are created specially.
  assert(kind != BEEV::SYMBOL);
  // so are these.

  // If all the parameters are constant, return the constant value.
  bool allConstant = true;
  for (unsigned i = 0; i < children.size(); i++)
    if (!children[i].isConstant())
      {
        allConstant = false;
        break;
      }

  assert(bm.hashingNodeFactory == &hashing);

  if (allConstant)
    {
      const ASTNode& hash = hashing.CreateTerm(kind, width, children);
      const ASTNode& c = NonMemberBVConstEvaluator(hash);
      assert(c.isConstant());
      return c;
    }

  ASTNode result;

  switch (kind)
    {

  case ITE:
    {
      if (children[0] == ASTTrue)
        result = children[1];
      else if (children[0] == ASTFalse)
        result = children[2];
      else if (children[1] == children[2])
        result = children[1];
      else if (children[2].GetKind() == ITE && (children[2][0] == children[0]))
        result = NodeFactory::CreateTerm(ITE, width, children[0], children[1], children[2][2]);
      else if (children[1].GetKind() == ITE && (children[1][0] == children[0]))
        result = NodeFactory::CreateTerm(ITE, width, children[0], children[1][1], children[2]);
      else if (children[0].GetKind() == BEEV::NOT)
        result = NodeFactory::CreateTerm(ITE, width, children[0][0], children[2], children[1]);
      else if (children[0].GetKind() == EQ && children[0][1] == children[1] && children[0][0].GetKind() == BEEV::BVCONST
          && children[0][1].GetKind() != BEEV::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0], children[0][0], children[2]);
      else if (children[0].GetKind() == EQ && children[0][0] == children[1] && children[0][1].GetKind() == BEEV::BVCONST
          && children[0][0].GetKind() != BEEV::BVCONST)
        result = NodeFactory::CreateTerm(ITE, width, children[0], children[0][1], children[2]);
      break;
    }

  case BEEV::BVMULT:
    {
      if (children.size() == 2)
        {
          if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
            result = bm.CreateZeroConst(width);

          else if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
            result = bm.CreateZeroConst(width);

          else if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
            result = children[0];

          else if (children[0].isConstant() && children[0] == bm.CreateOneConst(width))
            result = children[1];

          else if (width == 1 && children[0] == children[1])
            result = children[0];

          else if (children[0].GetKind() == BVUMINUS && children[1].GetKind() == BVUMINUS)
            result = NodeFactory::CreateTerm(BEEV::BVMULT, width, children[0][0], children[1][0]);
          else if (children[0].GetKind() == BVUMINUS)
            {
              result = NodeFactory::CreateTerm(BEEV::BVMULT, width, children[0][0], children[1]);
              result = NodeFactory::CreateTerm(BVUMINUS, width, result);
            }
          else if (children[1].GetKind() == BVUMINUS)
            {
              result = NodeFactory::CreateTerm(BEEV::BVMULT, width, children[1][0], children[0]);
              result = NodeFactory::CreateTerm(BVUMINUS, width, result);
            }
        }
      else if (children.size() > 2)
        {
          //Never create multiplications with arity > 2.

          deque<ASTNode> names;

          for (unsigned i = 0; i < children.size(); i++)
            names.push_back(children[i]);

          while (names.size() > 1)
            {
              ASTNode a = names.front();
              names.pop_front();

              ASTNode b = names.front();
              names.pop_front();

              ASTNode n = NodeFactory::CreateTerm(BVMULT, a.GetValueWidth(), a, b);
              names.push_back(n);
            }
          result = names.front();
        }
    }
    break;

  case BEEV::BVLEFTSHIFT:
    {
      if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = BEEV::Simplifier::convertKnownShiftAmount(kind, children, bm, &hashing);
      else if (width == 1 && children[0] == children[1])
        result = bm.CreateZeroConst(1);
      else if (children[0].GetKind() == BVUMINUS)
        result = NodeFactory::CreateTerm(BVUMINUS, width,
            NodeFactory::CreateTerm(BEEV::BVLEFTSHIFT, width, children[0][0], children[1]));
    }
    break;

  case BVRIGHTSHIFT:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);
      if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (children[1].isConstant())
        result = BEEV::Simplifier::convertKnownShiftAmount(kind, children, bm, &hashing);
      else if (children[0].isConstant() && children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)), children[0],
            bm.CreateZeroConst(width));
      else if ( width >= 3 && children[0].GetKind() == BVNEG && children[1] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVRIGHTSHIFT,width,bm.CreateMaxConst(width),children[0][0]);//320 -> 170
      else if ( width >= 3  && children[1].GetKind() == BVNEG && children[1][0] == children[0] )
        result =  NodeFactory::CreateTerm(BVRIGHTSHIFT,width,bm.CreateMaxConst(width),children[1]);//320 -> 170
      else if ( width >= 3 && children[0].GetKind() == BVUMINUS && children[1].GetKind() == BVNEG && children[1][0] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVDIV,width,bm.CreateOneConst(width),children[1]);//402 -> 76
      else if ( width >= 3 && children[0].GetKind() == BVNEG && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVUMINUS,width,NodeFactory::CreateTerm(ITE,width,NodeFactory::CreateNode(EQ,bm.CreateZeroConst(width),children[0][0]),bm.CreateOneConst(width),bm.CreateZeroConst(width)));//391 -> 70
    }
    break;

  case BEEV::BVSRSHIFT:
    {
      if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);
      else if (width > 1 && children[0].isConstant() && children[0] == bm.CreateOneConst(width))
        result = NodeFactory::CreateTerm(ITE, width,
            NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)), children[0],
            bm.CreateZeroConst(width));
      else if (children[0].isConstant() && CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
        result = bm.CreateMaxConst(width);
      else if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];
      else if (width == 1 && children[0] == children[1])
        result = children[0];
      else if ((children[0] == children[1]) || (children[0].GetKind() == BVUMINUS && children[0][0] == children[1]))
        {
          assert(width >1);
          ASTNode extract = NodeFactory::CreateTerm(BVEXTRACT, 1, children[0], bm.CreateBVConst(32, width - 1),
              bm.CreateBVConst(32, width - 1));
          result = NodeFactory::CreateTerm(BEEV::BVSX, width, extract, bm.CreateBVConst(32, width));
        }
      else if (width == 1 && children[1].isConstant() && children[1] == bm.CreateOneConst(1))
        result = children[0];
      else if (children[1].isConstant())
        result = BEEV::Simplifier::convertArithmeticKnownShiftAmount(kind, children, bm, &hashing);
      else if (children[1].GetKind() == BVUMINUS && children[0] == children[1][0])
        result = NodeFactory::CreateTerm(BEEV::BVSRSHIFT, width, children[0], children[1][0]);
      else if (children[0].isConstant() && !CONSTANTBV::BitVector_bit_test(children[0].GetBVConst(), width - 1))
        result = NodeFactory::CreateTerm(BVRIGHTSHIFT, width, children[0], children[1]);
      else if ( width >= 3 && children[0].GetKind() == BVNEG && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVSRSHIFT,width,children[0],children[0][0]);//414 -> 361


    }
    break;

  case BEEV::BVSUB:
    if (children.size() == 2)
      {
        if (children.size() == 2 && children[0] == children[1])
          result = bm.CreateZeroConst(width);
        else if (children.size() == 2 && children[1] == bm.CreateZeroConst(width))
          result = children[0];
        else
          result = NodeFactory::CreateTerm(BVPLUS, width, children[0],
              NodeFactory::CreateTerm(BVUMINUS, width, children[1]));
      }
    break;

  case BEEV::BVOR:
    {
      if (children.size() == 2)
        {
          if (children[0] == children[1])
            result = children[0];

          if (children[0].isConstant() && CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
            result = bm.CreateMaxConst(width);

          if (children[1].isConstant() && CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
            result = bm.CreateMaxConst(width);

          if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
            result = children[0];

          if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
            result = children[1];

          if (children[1].GetKind() == BVNEG && children[0] == children[1][0])
            result = bm.CreateMaxConst(width);
          if (children[0].GetKind() == BVNEG && children[1] == children[0][0])
            result = bm.CreateMaxConst(width);
        }
    }
    break;

  case BEEV::BVXOR:
    if (children.size() == 2)
      {
        if (children[0] == children[1])
          result = bm.CreateZeroConst(width);
        if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
          result = children[0];

        if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
          result = children[1];

        if (children[1].isConstant() && CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
          result = NodeFactory::CreateTerm(BVNEG, width, children[0]);

        if (children[0].isConstant() && CONSTANTBV::BitVector_is_full(children[0].GetBVConst()))
          result = NodeFactory::CreateTerm(BVNEG, width, children[1]);

        if (children[1].GetKind() == BVNEG && children[1][0] == children[0])
          result = bm.CreateMaxConst(width);

        if (children[0].GetKind() == BVNEG && children[0][0] == children[1])
          result = bm.CreateMaxConst(width);
        if ( width >= 3 &&  children.size() ==2 && children[0].GetKind() == BVNEG && children[1].GetKind() == BVNEG )
          result =  NodeFactory::CreateTerm(BVXOR,width,children[1][0],children[0][0]);//133 -> 133
      }
    break;

  case BEEV::BVAND:
    {

      bool oneFound = false;
      bool zeroFound = false;

      for (int i = 0; i < children.size(); i++)
        {
          if (children[i].GetKind() == BEEV::BVCONST)
            {
              if (CONSTANTBV::BitVector_is_full(children[i].GetBVConst()))
                oneFound = true;
              else if (CONSTANTBV::BitVector_is_empty(children[i].GetBVConst()))
                zeroFound = true;

            }
        }

      if (zeroFound)
        {
          result = bm.CreateZeroConst(width);
        }
      else if (oneFound)
        {
          ASTVec new_children;
          for (int i = 0; i < children.size(); i++)
            {
              if (children[i].GetKind() != BEEV::BVCONST || !CONSTANTBV::BitVector_is_full(children[i].GetBVConst()))
                new_children.push_back(children[i]);
            }

          assert(new_children.size() != 0);
          // constant. Should have been handled earlier.
          if (new_children.size() == 1)
            {
              result = new_children[0];
            }
          else
            result = hashing.CreateTerm(kind, width, new_children);
        }
    }

    if (children.size() == 2 && children[0] == children[1])
      {
        result = children[0];
      }

    // If there is just one run of 1 bits, replace by an extract and a concat.
    // i.e. 00011111111000000 & x , will be replaced by an extract of x just where
    // there are one bits. This should
    if (children.size() == 2 && (children[0].isConstant() || children[1].isConstant()))
      {
        ASTNode c0 = children[0];
        ASTNode c1 = children[1];
        if (c1.isConstant())
          {
            ASTNode t = c0;
            c0 = c1;
            c1 = t;
          }

        int start = -1;
        int end = -1;
        BEEV::CBV c = c0.GetBVConst();
        bool bad = false;
        for (int i = 0; i < width; i++)
          {
            if (CONSTANTBV::BitVector_bit_test(c, i))
              if (start == -1)
                start = i; // first one bit.
              else if (end != -1)
                bad = true;

            if (!CONSTANTBV::BitVector_bit_test(c, i))
              if (start != -1 && end == -1)
                end = i - 1; // end of run.
          }
        if (start != -1 && end == -1)
          end = width - 1;

        if (!bad && start != -1)
          {
            assert(end != -1);

            result = NodeFactory::CreateTerm(BVEXTRACT, end - start + 1, c1, bm.CreateBVConst(32, end),
                bm.CreateBVConst(32, start));

            if (start > 0)
              {
                ASTNode z = bm.CreateZeroConst(start);
                result = NodeFactory::CreateTerm(BVCONCAT, end + 1, result, z);
              }
            if (end < width - 1)
              {
                ASTNode z = bm.CreateZeroConst(width - end - 1);
                result = NodeFactory::CreateTerm(BVCONCAT, width, z, result);
              }
          }
      }

    if (children.size() == 2)
      {
        if (children[1].GetKind() == BVNEG && children[1][0] == children[0])
          result = bm.CreateZeroConst(width);
        if (children[0].GetKind() == BVNEG && children[0][0] == children[1])
          result = bm.CreateZeroConst(width);
      }
    break;

  case BEEV::BVSX:
    {
      if (width == children[0].GetValueWidth())
        result = children[0];
      break;
    }

  case BVNEG:
    if (children[0].GetKind() == BVNEG)
      result = children[0][0];
    if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 && children[0][0].GetKind() == BEEV::BVCONST
        && children[0][0] == bm.CreateMaxConst(width))
      result = NodeFactory::CreateTerm(BVUMINUS, width, children[0][1]);
    if (children[0].GetKind() == BVUMINUS)
      result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0], bm.CreateMaxConst(width));
    if (children[0].GetKind() == BVMOD && children[0][0].GetKind() == BVNEG && children[0][1].GetKind() == BVUMINUS
        && children[0][1][0] == children[0][0][0])
      result = children[0][0][0];

    break;

  case BVUMINUS:
    if (children[0].GetKind() == BVUMINUS)
      result = children[0][0];
    else if (width == 1)
      result = children[0];
    else if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 && children[0][0].GetKind() == BEEV::BVCONST
        && children[0][0] == bm.CreateOneConst(width))
      result = NodeFactory::CreateTerm(BVNEG, width, children[0][1]);
    else if (children[0].GetKind() == BVNEG)
      result = NodeFactory::CreateTerm(BVPLUS, width, children[0][0], bm.CreateOneConst(width));
    else if (children[0].GetKind() == BEEV::BVSX && children[0][0].GetValueWidth() == 1)
      result = NodeFactory::CreateTerm(BVCONCAT, width, bm.CreateZeroConst(width - 1), children[0][0]);
    else if (children[0].GetKind() == BVMULT && children[0].Degree() == 2 && children[0][0] == bm.CreateMaxConst(width))
      result = children[0][1];
    break;

  case BVEXTRACT:
    if (width == children[0].GetValueWidth())
      result = children[0];
    else if (BVEXTRACT == children[0].GetKind()) // reduce an extract over an extract.
      {
        const unsigned outerLow = children[2].GetUnsignedConst();
        const unsigned outerHigh = children[1].GetUnsignedConst();

        const unsigned innerLow = children[0][2].GetUnsignedConst();
        const unsigned innerHigh = children[0][1].GetUnsignedConst();
        result = NodeFactory::CreateTerm(BVEXTRACT, width, children[0][0], bm.CreateBVConst(32, outerHigh + innerLow),
            bm.CreateBVConst(32, outerLow + innerLow));
      }
    else if (BVCONCAT == children[0].GetKind())
      {
        // If the extract doesn't cross the concat, then remove the concat.
        const ASTNode& a = children[0][0];
        const ASTNode& b = children[0][1];

        const unsigned low = children[2].GetUnsignedConst();
        const unsigned high = children[1].GetUnsignedConst();

        if (high < b.GetValueWidth()) // Extract entirely from the lower value (b).
          {
            result = NodeFactory::CreateTerm(BVEXTRACT, width, b, children[1], children[2]);
          }
        if (low >= b.GetValueWidth()) // Extract entirely from the upper value (a).
          {
            ASTNode i = bm.CreateBVConst(32, high - b.GetValueWidth());
            ASTNode j = bm.CreateBVConst(32, low - b.GetValueWidth());
            result = NodeFactory::CreateTerm(BVEXTRACT, width, a, i, j);
          }
      }
    else if (BVUMINUS == children[0].GetKind() && children[1] == bm.CreateZeroConst(children[1].GetValueWidth())
        && children[2] == bm.CreateZeroConst(children[2].GetValueWidth()))
      {
        result = NodeFactory::CreateTerm(BVEXTRACT, width, children[0][0], children[1], children[2]);
      }
    break;

  case BVPLUS:
    if (children.size() == 2)
      {
        result = plusRules(children[0], children[1]);
        if (result.IsNull())
          result = plusRules(children[1], children[0]);
      }
    break;

  case SBVMOD:
    {
      const ASTNode max = bm.CreateMaxConst(width);

    if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
      result = children[0];
    else if (children[0] == children[1])
      result = bm.CreateZeroConst(width);
    else if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
      result = bm.CreateZeroConst(width);
    else if (children[1].isConstant() && children[1] == bm.CreateMaxConst(width))
      result = bm.CreateZeroConst(width);
    else if (children[0].isConstant() && children[0] == bm.CreateZeroConst(width))
      result = bm.CreateZeroConst(width);
    else if (children[0].GetKind() == BVUMINUS && children[0][0] == children[1])
      result = bm.CreateZeroConst(width);
    else if (children[1].GetKind() == BVUMINUS && children[1][0] == children[0])
      result = bm.CreateZeroConst(width);
#if 0
    else if ( width >= 4 && children[0].GetKind() == BVNEG && children[1] == children[0][0] )
      result = bm.CreateTerm(SBVMOD,width,max,children[0][0]);//9759 -> 542 | 4842 ms
    else if ( width >= 4 && children[1].GetKind() == BVNEG && children[1][0] == children[0] )
      result =  bm.CreateTerm(SBVMOD,width,max,children[1]);//9759 -> 542 | 4005 ms
    else if ( width >= 4 &&  children[0].GetKind() == BVNEG && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0] )
      result =  bm.CreateTerm(SBVMOD,width,max,children[1]);//9807 -> 674 | 2962 ms
#endif
    }

    break;

  case BEEV::BVDIV:
    if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
      result = children[0];
    if (children[1].isConstant() && CONSTANTBV::BitVector_bit_test(children[1].GetBVConst(), width - 1))
      {
        // We are dividing by something that has a one in the MSB. It's either 1 or zero.
        result = NodeFactory::CreateTerm(ITE, width, NodeFactory::CreateNode(BEEV::BVGE, children[0], children[1]),
            bm.CreateOneConst(width), bm.CreateZeroConst(width));
      }
    else if (children[1].isConstant() && children[1] == bm.CreateZeroConst(width)
        && bm.UserFlags.division_by_zero_returns_one_flag)
      result = bm.CreateOneConst(width);
    else if (bm.UserFlags.division_by_zero_returns_one_flag && children[0] == children[1])
      result = bm.CreateOneConst(width);
    else if (bm.UserFlags.division_by_zero_returns_one_flag && children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = NodeFactory::CreateTerm(ITE,width, NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)) ,bm.CreateOneConst(width),bm.CreateZeroConst(width));
    else if (bm.UserFlags.division_by_zero_returns_one_flag &&  width >= 2 && children[0].GetKind() == BVNEG && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0])
      result = NodeFactory::CreateTerm(ITE,width,NodeFactory::CreateNode(EQ,bm.CreateZeroConst(width),children[0][0]),bm.CreateOneConst(width),bm.CreateZeroConst(width));

    break;

  case SBVDIV:
    if (children[1].isConstant() && children[1] == bm.CreateOneConst(width))
      result = children[0];
    else if (children[0] == children[1] && bm.UserFlags.division_by_zero_returns_one_flag)
      result = bm.CreateOneConst(width);
    else if (children[1].GetKind() == BVUMINUS && children[0] == children[1][0]
        && bm.UserFlags.division_by_zero_returns_one_flag)
      result = NodeFactory::CreateTerm(SBVDIV, width, children[1], children[0]);
    else if (bm.UserFlags.division_by_zero_returns_one_flag && children[0].isConstant()
        && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
      result = NodeFactory::CreateTerm(ITE, width, NodeFactory::CreateNode(EQ, children[1], bm.CreateZeroConst(width)),
          bm.CreateOneConst(width), bm.CreateZeroConst(width));
    if (children[1].isConstant() && CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
      result = NodeFactory::CreateTerm(BVUMINUS, width, children[0]);
    break;

  case SBVREM:
    {
      const ASTNode one = bm.CreateOneConst(width);
          const ASTNode zero = bm.CreateZeroConst(width);
          const ASTNode max = bm.CreateMaxConst(width);

    if (children[0] == children[1])
      result = bm.CreateZeroConst(width);
    else if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
      result = bm.CreateZeroConst(width);
    else if (children[1].isConstant() && CONSTANTBV::BitVector_is_full(children[1].GetBVConst()))
      result = bm.CreateZeroConst(width);
    else if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
      result = children[0];
    else if (children[1].isConstant() && bm.CreateOneConst(width) == children[1])
      result = bm.CreateZeroConst(width);
    else if (children[1].GetKind() == BVUMINUS)
      result = NodeFactory::CreateTerm(SBVREM, width, children[0], children[1][0]);
    else if (children[0].GetKind() == BVUMINUS && children[0][0] == children[1])
      result = bm.CreateZeroConst(width);
#if 0
    else if ( width >= 4 &&  children[0].GetKind() == BVNEG && children[1] == children[0][0] )
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVMOD,width,one,children[0][0]));//9350 -> 624 | 3072 ms
    else if ( width >= 4 &&  children[1].GetKind() == BVNEG && children[1][0] == children[0] )
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVMOD,width,one,children[1]));//9350 -> 624 | 2402 ms
    else if ( width >= 4 &&  children[0].GetKind() == BVUMINUS && children[1] == max)
      result =  bm.CreateTerm(BVUMINUS,width,bm.CreateTerm(SBVREM,width,children[0][0],children[1]));//123 -> 83 | 1600 ms
#endif
    }


    break;

  case BVMOD:
    {
      if (children[0] == children[1])
        result = bm.CreateZeroConst(width);

      if (children[0].isConstant() && CONSTANTBV::BitVector_is_empty(children[0].GetBVConst()))
        result = bm.CreateZeroConst(width);

      if (children[1].isConstant() && CONSTANTBV::BitVector_is_empty(children[1].GetBVConst()))
        result = children[0];

      if (children[0].GetKind() == BVPLUS && children[0].Degree() == 2 && children[0][0] == bm.CreateMaxConst(width)
          && children[1] == children[0][1])
        result = children[0];

      const ASTNode one = bm.CreateOneConst(width);

      if (children[0].GetKind() == BVNEG && children[1].GetKind() == BVUMINUS && children[1][0] == children[0][0])
        result = children[0];

      if (children[1].isConstant() && children[1] == one)
        result = bm.CreateZeroConst(width);

      if (children[0].isConstant() && children[0] == one)
        result = NodeFactory::CreateTerm(ITE, width, NodeFactory::CreateNode(EQ, children[1], one),
            bm.CreateZeroConst(width), one);
#if 0
      if ( width >= 3 && children[0].GetKind() == BVNEG && children[1] == children[0][0] )
        result =  NodeFactory::CreateTerm(BVMOD,width,bm.CreateMaxConst(width),children[0][0]);//3285 -> 3113

      if ( width >= 3 && children[1].GetKind() == BVNEG && children[1][0] == children[0] )
        result =  NodeFactory::CreateTerm(BVMOD,width,bm.CreateMaxConst(width),children[1]);//3285 -> 3113

      if ( width >= 4 && children[0].GetKind() == BVUMINUS && children[1].GetKind() == BVNEG && children[1][0] == children[0][0] )
        result  =   NodeFactory::CreateTerm(SBVREM,width,one,children[1]); //8883 -> 206 | 1566 ms
#endif
    }

    break;

  case BEEV::WRITE:
    if (children[0].GetKind() == BEEV::WRITE && children[1] == children[0][1])
      {
        // If the indexes of two writes are the same, then discard the inner write.
        result = NodeFactory::CreateArrayTerm(BEEV::WRITE, children[0].GetIndexWidth(), children[0].GetValueWidth(),
            children[0][0], children[1], children[2]);
      }
    else if (children[2].GetKind() == BEEV::READ && children[0] == children[2][0] && children[1] == children[2][1])
      {
        // Its writing into the array what's already there. i.e.  a[i] = a[i]
        result = children[0];
      }
    break;

  case BEEV::READ:
    if (children[0].GetKind() == BEEV::WRITE)
      {
        result = chaseRead(children, width);
      }
    break;

  default: // quieten compiler.
    break;
    }

  if (result.IsNull())
    result = hashing.CreateTerm(kind, width, children);

  return result;
}
