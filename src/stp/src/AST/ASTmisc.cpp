// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#include "AST.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/NodeIterator.h"

namespace BEEV
{
  
  /****************************************************************
   * Universal Helper Functions                                   *
   ****************************************************************/

  void process_argument(const char ch, STPMgr  *bm)
  {
    switch(ch)
        {
        case 'a' :
          bm->UserFlags.optimize_flag = false;
          break;
        case 'c':
          bm->UserFlags.construct_counterexample_flag = true;
          break;
        case 'd':
          bm->UserFlags.construct_counterexample_flag = true;
          bm->UserFlags.check_counterexample_flag = true;
          break;

        case 'h':
          fprintf(stderr,usage,prog);
          cout << helpstring;
          exit(-1);
          break;
        case 'm':
          bm->UserFlags.smtlib1_parser_flag=true;
          bm->UserFlags.division_by_zero_returns_one_flag = true;
                      if (bm->UserFlags.smtlib2_parser_flag)
                              FatalError("Can't use both the smtlib and smtlib2 parsers");
          break;
        case 'n':
          bm->UserFlags.print_output_flag = true;
          break;
        case 'p':
          bm->UserFlags.print_counterexample_flag = true;
          break;
        case 'q':
          bm->UserFlags.print_arrayval_declaredorder_flag = true;
          break;
        case 'r':
          bm->UserFlags.ackermannisation = true;
          break;
        case 's' :
          bm->UserFlags.stats_flag = true;
          break;
        case 't':
          bm->UserFlags.quick_statistics_flag = true;
          break;
        case 'v' :
          bm->UserFlags.print_nodes_flag = true;
          break;
        case 'w':
          bm->UserFlags.wordlevel_solve_flag = false;
          break;
        case 'x':
          bm->UserFlags.xor_flatten_flag = true;
          break;
        case 'y':
          bm->UserFlags.print_binary_flag = true;
          break;
        case 'z':
          bm->UserFlags.print_sat_varorder_flag = true;
          break;
        default:
          fprintf(stderr,usage,prog);
          cout << helpstring;
          exit(-1);
          break;
        }
  }

  // Sort ASTNodes by expression numbers
  bool exprless(const ASTNode n1, const ASTNode n2)
  {
    return (n1.GetNodeNum() < n2.GetNodeNum());
  }

  // This is for sorting by arithmetic expressions (for
  // combining like terms, etc.)
  bool arithless(const ASTNode n1, const ASTNode n2)
  {
    Kind k1 = n1.GetKind();
    Kind k2 = n2.GetKind();

    if (n1 == n2)
      {
        // necessary for "strict weak ordering"
        return false;
      }
    else if (BVCONST == k1 && BVCONST != k2)
      {
        // put consts first
        return true;
      }
    else if (BVCONST != k1 && BVCONST == k2)
      {
        // put consts first
        return false;
      }
    else if (SYMBOL == k1 && SYMBOL != k2)
      {
        // put symbols next
        return true;
      }
    else if (SYMBOL != k1 && SYMBOL == k2)
      {
        // put symbols next
        return false;
      }
    else
      {
        // otherwise, sort by exprnum (descendents will appear
        // before ancestors).
        return (n1.GetNodeNum() < n2.GetNodeNum());
      }
  } //end of arithless


  // counts the number of reads. Shortcut when we get to the limit.
  void
  numberOfReadsLessThan(const ASTNode& n, hash_set<int> & visited, int& soFar, const int limit)
  {
    if (n.isAtom())
      return;

    if (visited.find(n.GetNodeNum()) != visited.end())
      return;

    if (n.GetKind() == READ)
      soFar++;

    if (soFar > limit)
      return;

    visited.insert(n.GetNodeNum());

    for (int i = 0; i < n.Degree(); i++)
      numberOfReadsLessThan(n[i], visited, soFar,limit);
  }

  // True if the number of reads in "n" is less than "limit"
  bool
  numberOfReadsLessThan(const ASTNode&n, int limit)
  {
    hash_set<int> visited;
    int reads = 0;
    numberOfReadsLessThan(n, visited, reads,limit);
    return reads < limit;
  }


    // True if any descendants are arrays.
    bool
    containsArrayOps(const ASTNode&n)
    {

      NodeIterator ni(n, n.GetSTPMgr()->ASTUndefined, *n.GetSTPMgr());
      ASTNode current;
      while ((current = ni.next()) != ni.end())
        if (current.GetIndexWidth()>0)
          return true;

      return false;
    }

	bool isCommutative(const Kind k) {
	switch (k) {
	case BVOR:
	case BVAND:
	case BVXOR:
	case BVNAND:
	case BVNOR:
	case BVXNOR:
	case BVPLUS:
	case BVMULT:
	case EQ:
	case AND:
	case OR:
	case NAND:
	case NOR:
	case XOR:
	case IFF:
	case BVNEG:
	case NOT:
	case BVUMINUS:
		return true;
	default:
		return false;
	}

	return false;
}


  void FatalError(const char * str, const ASTNode& a, int w)
  {
    if (a.GetKind() != UNDEFINED)
      {
        cerr << "Fatal Error: " << str << endl << a << endl;
        cerr << w << endl;
      }
    else
      {
        cerr << "Fatal Error: " << str << endl;
        cerr << w << endl;
      }
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    assert(0); // gdb will stop here giving a stacktrace.
    exit(-1);
  }

  void FatalError(const char * str)
  {
    cerr << "Fatal Error: " << str << endl;
    if (vc_error_hdlr)
      vc_error_hdlr(str);
    assert(0);
    exit(-1);

  }
  
  void SortByExprNum(ASTVec& v)
  {
    sort(v.begin(), v.end(), exprless);
  }

  void SortByArith(ASTVec& v)
  {
    sort(v.begin(), v.end(), arithless);
  }

  bool isAtomic(Kind kind)
  {
    if (TRUE == kind  || FALSE == kind || 
        EQ == kind    ||
        BVLT == kind  || BVLE == kind  || 
        BVGT == kind  || BVGE == kind  || 
        BVSLT == kind || BVSLE == kind || 
        BVSGT == kind || BVSGE == kind || 
        SYMBOL == kind || BVGETBIT == kind)
      return true;
    return false;
  }


  // If there is a lot of sharing in the graph, this will take a long
  // time.  it doesn't mark subgraphs as already having been
  // typechecked.
  bool BVTypeCheckRecursive(const ASTNode& n)
  {
    const ASTVec& c = n.GetChildren();

    BVTypeCheck(n);

    for (ASTVec::const_iterator it = c.begin(), itend = c.end(); it != itend; it++)
      BVTypeCheckRecursive(*it);

    return true;
  }

  void buildListOfSymbols(const ASTNode& n, ASTNodeSet& visited,
  		ASTNodeSet& symbols)
  {
  	if (visited.find(n) != visited.end())
  		return; // already visited.

  	visited.insert(n);

  	if (n.GetKind() == SYMBOL)
  	{
  		symbols.insert(n);
  	}

  	for (unsigned i = 0; i < n.GetChildren().size(); i++)
  		buildListOfSymbols(n[i], visited, symbols);
  }


  void checkChildrenAreBV(const ASTVec& v, const ASTNode&n) {
	for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
		if (BITVECTOR_TYPE != it->GetType()) {
			cerr << "The type is: " << it->GetType() << endl;
			FatalError(
					"BVTypeCheck:ChildNodes of bitvector-terms must be bitvectors\n",
					n);
		}
}

  void FlattenKind(const Kind k, const ASTVec &children, ASTVec & flat_children)
  {
    ASTVec::const_iterator ch_end = children.end();
    for (ASTVec::const_iterator it = children.begin(); it != ch_end; it++)
      {
        Kind ck = it->GetKind();
        if (k == ck)
          {
            FlattenKind(k,it->GetChildren(), flat_children);
          }
        else
          {
            flat_children.push_back(*it);
          }
      }
  }

  // Flatten (k ... (k ci cj) ...) to (k ... ci cj ...)
  ASTVec FlattenKind(Kind k, const ASTVec &children)
  {
    ASTVec flat_children;
    FlattenKind(k,children,flat_children);
    return flat_children;
  }


  /* FUNCTION: Typechecker for terms and formulas
   *
   * TypeChecker: Assumes that the immediate Children of the input
   * ASTNode have been typechecked. This function is suitable in
   * scenarios like where you are building the ASTNode Tree, and you
   * typecheck as you go along. It is not suitable as a general
   * typechecker.
   *
   * If this returns, this ALWAYS returns true. If there is an error it
   * will call FatalError() and abort.
   */
  bool BVTypeCheck(const ASTNode& n)
  {
    Kind k = n.GetKind();
    //The children of bitvector terms are in turn bitvectors.
    const ASTVec& v = n.GetChildren();
    if (is_Term_kind(k))
      {
        switch (k)
          {
          case BVCONST:
            if (BITVECTOR_TYPE != n.GetType())
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            break;
          case SYMBOL:
            return true;
          case ITE:
  			if (n.Degree() != 3)
  				FatalError("BVTypeCheck: should have exactly 3 args\n", n);
        	if (BOOLEAN_TYPE != n[0].GetType() || (n[1].GetType() != n[2].GetType()))
              FatalError("BVTypeCheck: The term t does not typecheck, where t = \n", n);
            if (n[1].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            if (n[1].GetIndexWidth() != n[2].GetIndexWidth())
              FatalError("BVTypeCheck: length of THENbranch != length of ELSEbranch in the term t = \n", n);
            break;
          case READ:
            if (n.GetChildren().size() !=2)
              FatalError("2 params to read.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              {
                cerr << "Length of indexwidth of array: " << n[0] << " is : " << n[0].GetIndexWidth() << endl;
                cerr << "Length of the actual index is: " << n[1] << " is : " << n[1].GetValueWidth() << endl;
                FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
              }
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            break;
          case WRITE:
            if (n.GetChildren().size() !=3)
              FatalError("3 params to write.");
            if (n[0].GetIndexWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: length of indexwidth of array != length of actual index in the term t = \n", n);
            if (n[0].GetValueWidth() != n[2].GetValueWidth())
              FatalError("BVTypeCheck: valuewidth of array != length of actual value in the term t = \n", n);
            if (ARRAY_TYPE != n[0].GetType())
              FatalError("First parameter to read should be an array", n[0]);
            if (BITVECTOR_TYPE != n[1].GetType())
              FatalError("Second parameter to read should be a bitvector", n[1]);
            if (BITVECTOR_TYPE != n[2].GetType())
              FatalError("Third parameter to read should be a bitvector", n[2]);

            break;

          case BVDIV:
          case BVMOD:
          case BVSUB:

          case SBVDIV:
          case SBVREM:
          case SBVMOD:

          case BVLEFTSHIFT:
          case BVRIGHTSHIFT:
          case BVSRSHIFT:
          case BVVARSHIFT:
        	  if (n.Degree() != 2)
        		  FatalError("BVTypeCheck: should have exactly 2 args\n", n);
        	  // run on.
          case BVOR:
          case BVAND:
          case BVXOR:
          case BVNOR:
          case BVNAND:
          case BVXNOR:

          case BVPLUS:
          case BVMULT:
            {
              if (!(v.size() >= 2))
                FatalError("BVTypeCheck:bitwise Booleans and BV arith operators must have at least two arguments\n", n);
              unsigned int width = n.GetValueWidth();
              for (ASTVec::const_iterator it = v.begin(), itend = v.end(); it != itend; it++)
                {
                  if (width != it->GetValueWidth())
                    {
                      cerr << "BVTypeCheck:Operands of bitwise-Booleans and BV arith operators must be of equal length\n";
                      cerr << n << endl;
                      cerr << "width of term:" << width << endl;
                      cerr << "width of offending operand:" << it->GetValueWidth() << endl;
                      FatalError("BVTypeCheck:Offending operand:\n", *it);
                    }
                  if (BITVECTOR_TYPE != it->GetType())
                    FatalError("BVTypeCheck: ChildNodes of bitvector-terms must be bitvectors\n", n);
                }
              break;
            }
          case BVSX:
          case BVZX:
			//in BVSX(n[0],len), the length of the BVSX term must be
			//greater than the length of n[0]
			if (n[0].GetValueWidth() > n.GetValueWidth()) {
				FatalError(
						"BVTypeCheck: BV[SZ]X(t,bv[sz]x_len) : length of 't' must be <= bv[sz]x_len\n",
						n);
			}
			if ((v.size() != 2))
				FatalError(
						"BVTypeCheck:BV[SZ]X must have two arguments. The second is the new width\n",
						n);
			break;

		case BVCONCAT:
			checkChildrenAreBV(v, n);
			if (n.Degree() != 2)
				FatalError("BVTypeCheck: should have exactly 2 args\n", n);
			if (n.GetValueWidth() != n[0].GetValueWidth()
					+ n[1].GetValueWidth())
				FatalError("BVTypeCheck:BVCONCAT: lengths do not add up\n", n);
			break;
		case BVUMINUS:
		case BVNEG:
			checkChildrenAreBV(v, n);
			if (n.Degree() != 1)
				FatalError("BVTypeCheck: should have exactly 1 args\n", n);
			if (n.GetValueWidth() != n[0].GetValueWidth())
		          FatalError("BVTypeCheck: should have same value width\n", n);
			break;
		case BVEXTRACT:
			checkChildrenAreBV(v, n);
			if (n.Degree() != 3)
				FatalError("BVTypeCheck: should have exactly 3 args\n", n);
			if (!(BVCONST == n[1].GetKind() && BVCONST == n[2].GetKind()))
				FatalError("BVTypeCheck: indices should be BVCONST\n", n);
			if (n.GetValueWidth() != n[1].GetUnsignedConst()
					- n[2].GetUnsignedConst() + 1)
				FatalError("BVTypeCheck: length mismatch\n", n);
			if (n[1].GetUnsignedConst() >= n[0].GetValueWidth())
				FatalError(
						"BVTypeCheck: Top index of select is greater or equal to the bitwidth.\n",
						n);
			break;
		default:
			cerr << _kind_names[k];
			FatalError("No type checking for type");
			break;
		}
      }
    else
      {
        if (!(is_Form_kind(k) && BOOLEAN_TYPE == n.GetType()))
          FatalError("BVTypeCheck: not a formula:", n);
        switch (k)
          {
          case TRUE:
          case FALSE:
          case SYMBOL:
            return true;
          case PARAMBOOL:
            if(2 != n.Degree())
              FatalError("BVTypeCheck: PARAMBOOL formula can have exactly two childNodes", n);
            break;
          case EQ:
  			if (n.Degree() != 2)
  				FatalError("BVTypeCheck: should have exactly 2 args\n", n);
        	if (!(n[0].GetValueWidth() == n[1].GetValueWidth() && n[0].GetIndexWidth() == n[1].GetIndexWidth()))
              {
                cerr << "valuewidth of lhs of EQ: " << n[0].GetValueWidth() << endl;
                cerr << "valuewidth of rhs of EQ: " << n[1].GetValueWidth() << endl;
                cerr << "indexwidth of lhs of EQ: " << n[0].GetIndexWidth() << endl;
                cerr << "indexwidth of rhs of EQ: " << n[1].GetIndexWidth() << endl;
                FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
              }
            break;
          case BVLT:
          case BVLE:
          case BVGT:
          case BVGE:
          case BVSLT:
          case BVSLE:
          case BVSGT:
          case BVSGE:
  			if (n.Degree() != 2)
  				FatalError("BVTypeCheck: should have exactly 2 args\n", n);
            if (BITVECTOR_TYPE != n[0].GetType() && BITVECTOR_TYPE != n[1].GetType())
              FatalError("BVTypeCheck: terms in atomic formulas must be bitvectors", n);
            if (n[0].GetValueWidth() != n[1].GetValueWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            if (n[0].GetIndexWidth() != n[1].GetIndexWidth())
              FatalError("BVTypeCheck: terms in atomic formulas must be of equal length", n);
            break;
          case NOT:
            if (1 != n.Degree())
              FatalError("BVTypeCheck: NOT formula can have exactly one childNode", n);
            break;
          case AND:
          case OR:
          case XOR:
          case NAND:
          case NOR:
            if (2 > n.Degree())
              FatalError("BVTypeCheck: AND/OR/XOR/NAND/NOR: must have atleast 2 ChildNodes", n);
            break;
          case IFF:
          case IMPLIES:
            if (2 != n.Degree())
              FatalError("BVTypeCheck:IFF/IMPLIES must have exactly 2 ChildNodes", n);
            break;
          case ITE:
            if (3 != n.Degree())
              FatalError("BVTypeCheck:ITE must have exactly 3 ChildNodes", n);
            break;
          default:
            FatalError("BVTypeCheck: Unrecognized kind: ");
            break;
          }
      }
    return true;
  } //End of TypeCheck function

  // callback for SIGALRM.
  void handle_time_out(int parameter){
    printf("Timed Out.\n");

    abort();
    // I replaced the exit(0) with an abort().
    // The exit was sometimes hanging, seemingly because of a bug somewhere else (e.g. loader, glibc).
    // In strace it output:

    //--- SIGVTALRM (Virtual timer expired) @ 0 (0) ---
    //fstat(1, {st_mode=S_IFCHR|0620, st_rdev=makedev(136, 5), ...}) = 0
    //mmap(NULL, 4096, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_ANONYMOUS, -1, 0) = 0x7fabca622000
    //write(1, "Timed Out.\n", 11Timed Out.
    //)            = 11
    //futex(0x7fabc9c54e40, FUTEX_WAIT, 2, NULL

    // Then it would just sit there waiting for the mutex (which never came).
    //exit(0);
  }


  itimerval timeout;
  void setHardTimeout(int sec)
  {
  signal(SIGVTALRM, handle_time_out);
  timeout.it_interval.tv_usec = 0;
  timeout.it_interval.tv_sec  = 0;
  timeout.it_value.tv_usec    = 0;
  timeout.it_value.tv_sec     = sec;
  setitimer(ITIMER_VIRTUAL, &timeout, NULL);
  }

  long getCurrentTime()
  {
    timeval t;
    gettimeofday(&t, NULL);
    return (1000 * t.tv_sec) + (t.tv_usec / 1000);
  }

};//end of namespace
