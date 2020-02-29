// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef STPMGR_H
#define STPMGR_H

#include "UserDefinedFlags.h"
#include "../AST/AST.h"
#include "../AST/NodeFactory/HashingNodeFactory.h"
#include "../sat/SATSolver.h"
#include "../boost/noncopyable.hpp"

namespace BEEV
{
  /*****************************************************************
   * Class STPMgr.  This holds all "global" variables for the system,
   * such as unique tables for the various kinds of nodes.
   *****************************************************************/

  class STPMgr : boost::noncopyable
  {
    friend class ASTNode;
    friend class ASTInterior;
    friend class ASTBVConst;
    friend class ASTSymbol;
    friend BEEV::ASTNode HashingNodeFactory::CreateNode(const Kind kind,	const BEEV::ASTVec & back_children);

  private:
    /****************************************************************
     * Private Typedefs and Data                                    *
     ****************************************************************/

    // Typedef for unique Interior node table.
    typedef HASHSET<
    ASTInterior *, 
    ASTInterior::ASTInteriorHasher, 
    ASTInterior::ASTInteriorEqual> ASTInteriorSet;    

    // Typedef for unique Symbol node (leaf) table.
    typedef HASHSET<
      ASTSymbol *, 
      ASTSymbol::ASTSymbolHasher, 
      ASTSymbol::ASTSymbolEqual> ASTSymbolSet;

    //Typedef for unique BVConst node (leaf) table.
    typedef HASHSET<
      ASTBVConst *, 
      ASTBVConst::ASTBVConstHasher, 
      ASTBVConst::ASTBVConstEqual> ASTBVConstSet;

#if 0
    typedef HASHMAP<
      ASTNode, 
      ASTNodeSet,
      ASTNode::ASTNodeHasher, 
      ASTNode::ASTNodeEqual> ASTNodeToSetMap;
#endif

    // Unique node tables that enables common subexpression sharing
    ASTInteriorSet _interior_unique_table;

    // Table for variable names, let names etc.
    ASTSymbolSet _symbol_unique_table;

    // Table to uniquefy bvconst
    ASTBVConstSet _bvconst_unique_table;

    // Global for assigning new node numbers.
    int _max_node_num;

    uint8_t last_iteration;

      public:
    HashingNodeFactory* hashingNodeFactory;
    NodeFactory *defaultNodeFactory;

    //frequently used nodes
    ASTNode ASTFalse, ASTTrue, ASTUndefined;

    volatile bool soft_timeout_expired;

    // No nodes should already have the iteration number that is returned from here.
    // This never returns zero.
    uint8_t getNextIteration()
    {
        if (last_iteration == 255)
            {
                resetIteration();
                last_iteration = 0;
            }

        uint8_t result =  ++last_iteration;
        assert(result != 0);
        return result;
    }

    // Detauls the iteration count back to zero.
    void resetIteration()
    {
        for (ASTInteriorSet::iterator it =_interior_unique_table.begin(); it != _interior_unique_table.end(); it++ )
            {(*it)->iteration = 0;}

        for (ASTSymbolSet ::iterator it =_symbol_unique_table.begin(); it != _symbol_unique_table.end(); it++ )
            {(*it)->iteration = 0;}

        for (ASTBVConstSet:: iterator it =_bvconst_unique_table.begin(); it != _bvconst_unique_table.end(); it++ )
            {(*it)->iteration = 0;}
    }

    int getAssertLevel()
    {
      return _asserts.size();
    }

  private:

    // Stack of Logical Context. each entry in the stack is a logical
    // context. A logical context is a vector of assertions. The
    // logical context is represented by a ptr to a vector of
    // assertions in that logical context. Logical contexts are
    // created by PUSH/POP
    std::vector<ASTVec*> _asserts;

    // Memo table that tracks terms already seen
    ASTNodeMap TermsAlreadySeenMap;
    
    // The query for the current logical context.
    ASTNode _current_query;    

    // Ptr to class that reports on the running time of various parts
    // of the code
    RunTimes * runTimes;

    /****************************************************************
     * Private Member Functions                                     *
     ****************************************************************/
    
    // Destructively appends back_child nodes to front_child nodes.
    // If back_child nodes is NULL, no appending is done.  back_child
    // nodes are not modified.  Then it returns the hashed copy of the
    // node, which is created if necessary.
    ASTInterior *CreateInteriorNode(Kind kind, 
                                    ASTInterior *new_node,
                                    const ASTVec & back_children = 
                                    _empty_ASTVec);

    // Create unique ASTInterior node.
    ASTInterior *LookupOrCreateInterior(ASTInterior *n);

    // Create unique ASTSymbol node.
    ASTSymbol *LookupOrCreateSymbol(ASTSymbol& s);

    // Called whenever we want to make sure that the Symbol is
    // declared during semantic analysis
    bool LookupSymbol(ASTSymbol& s);

    // Called by ASTNode constructors to uniqueify ASTBVConst
    ASTBVConst *LookupOrCreateBVConst(ASTBVConst& s);
  
    // Cache of zero/one/max BVConsts of different widths.
    ASTVec zeroes;
    ASTVec ones;
    ASTVec max;

    // Set of new symbols introduced that replace the array read terms
    ASTNodeSet Introduced_SymbolsSet;

    CBV CreateBVConstVal;

  public:

    bool LookupSymbol(const char * const name);
    bool LookupSymbol(const char * const name, ASTNode& output);
    
    /****************************************************************
     * Public Flags                                                 *
     ****************************************************************/    
    UserDefinedFlags UserFlags;
    
    // This flag, when true, indicates that counterexample is being
    // checked by the counterexample checker
    bool counterexample_checking_during_refinement;

    // This flag indicates as to whether the input has been determined
    // to be valid or not by this tool
    bool ValidFlag;

    // This flag, when true, indicates that a BVDIV divide by zero
    // exception occured. However, the program must not exit with a
    // fatalerror. Instead, it should evaluate the whole formula
    // (which contains the BVDIV term) to be FALSE.
    bool bvdiv_exception_occured;

    // Flags indicates that counterexample will now be checked by the
    // counterexample checker, and hence simplifyterm must switch off
    // certain optimizations. In particular, array write optimizations
    //bool start_abstracting;
    //bool Begin_RemoveWrites;
    bool SimplifyWrites_InPlace_Flag;
   
    //count is used in the creation of new variables
    unsigned int _symbol_count;

    // The value to append to the filename when saving the CNF.
    unsigned int CNFFileNameCounter;

    /****************************************************************
     * Public Member Functions                                      *
     ****************************************************************/

    // Constructor
    STPMgr() : 
      _symbol_unique_table(),
      _bvconst_unique_table(),
      _interior_unique_table(),
      UserFlags(),
      _symbol_count(0),
      CNFFileNameCounter(0),
      last_iteration(0),
      soft_timeout_expired(false)

    {
      _max_node_num = 0;
      //Begin_RemoveWrites = false;
      ValidFlag = false;
      bvdiv_exception_occured = false;
      counterexample_checking_during_refinement = false;
      //start_abstracting = false;
      //Begin_RemoveWrites = false;
      SimplifyWrites_InPlace_Flag = false;      

      // Need to initiate the node factories before any nodes are created.
      hashingNodeFactory = new HashingNodeFactory(*this);
      defaultNodeFactory= hashingNodeFactory;

      ASTFalse     = CreateNode(FALSE);
      ASTTrue      = CreateNode(TRUE); 
      ASTUndefined = CreateNode(UNDEFINED);
      runTimes     = new RunTimes();
      _current_query = ASTUndefined;
      CreateBVConstVal = NULL;
    }    
    
    RunTimes * GetRunTimes(void)
    {
      return runTimes;
    }

#if 0
    void SetRemoveWritesFlag(bool in)
    {
      Begin_RemoveWrites = in;
    }

    bool GetRemoveWritesFlag(void)
    {
      return Begin_RemoveWrites;
    }
#endif

    int NewNodeNum()
    {
      _max_node_num += 2;
      return _max_node_num;
    }

    unsigned int NodeSize(const ASTNode& a);

    /****************************************************************
     * Simplifying create formula functions                         *
     ****************************************************************/

    // Simplifying create functions
    ASTNode CreateSimpForm(Kind kind, 
                           ASTVec &children);
    ASTNode CreateSimpForm(Kind kind, 
                           const ASTNode& child0);
    ASTNode CreateSimpForm(Kind kind, 
                           const ASTNode& child0, 
                           const ASTNode& child1);
    ASTNode CreateSimpForm(Kind kind, 
                           const ASTNode& child0,
                           const ASTNode& child1, 
                           const ASTNode& child2);
    ASTNode CreateSimpNot (const ASTNode& form);

    ASTNode CreateSimpXor(const ASTNode& form1, 
                          const ASTNode& form2);
    ASTNode CreateSimpXor(ASTVec &children);
    ASTNode CreateSimpAndOr(bool isAnd, 
                            const ASTNode& form1,
                            const ASTNode& form2);
    ASTNode CreateSimpAndOr(bool IsAnd, 
                            ASTVec &children);
    ASTNode CreateSimpFormITE(const ASTNode& child0, 
                              const ASTNode& child1,
                              const ASTNode& child2);

    /****************************************************************
     * Create Symbol and BVConst functions                          *
     ****************************************************************/

    // Create and return an ASTNode for a symbol
    ASTNode LookupOrCreateSymbol(const char * const name);

    // Create and return an ASTNode for a symbol Width is number of
    // bits.
    ASTNode CreateOneConst(unsigned int width);
    ASTNode CreateTwoConst(unsigned int width);
    ASTNode CreateMaxConst(unsigned int width);
    ASTNode CreateZeroConst(unsigned int width);
    ASTNode CreateBVConst(CBV bv, unsigned width);
    ASTNode CreateBVConst(const char *strval, int base);
    ASTNode CreateBVConst(string strval, int base, int bit_width);
    ASTNode CreateBVConst(unsigned int width, unsigned long long int bvconst);
    ASTNode charToASTNode(unsigned char* strval, int base , int bit_width);
    
    /****************************************************************
     * Create Node functions                                        *
     ****************************************************************/

    inline ASTNode CreateSymbol(const char * const name, unsigned indexWidth, unsigned valueWidth)
    {
      return defaultNodeFactory->CreateSymbol(name,indexWidth,valueWidth);
    }


    // Create and return an interior ASTNode
    inline BEEV::ASTNode CreateNode(BEEV::Kind kind, const BEEV::ASTVec& children = _empty_ASTVec)
    {
   	 return defaultNodeFactory->CreateNode(kind,children);
    }

    inline ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTVec & back_children = _empty_ASTVec)
    {
  	   	  return defaultNodeFactory->CreateNode(kind, child0, back_children);
    }

    inline ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1, const ASTVec & back_children = _empty_ASTVec)
    {
 	   	  return defaultNodeFactory->CreateNode(kind, child0, child1, back_children);
    }

    inline   ASTNode CreateNode(Kind kind, const ASTNode& child0, const ASTNode& child1, const ASTNode& child2, const ASTVec & back_children = _empty_ASTVec)
    {
   	 return defaultNodeFactory->CreateNode(kind, child0, child1, child2, back_children);

    }

    /****************************************************************
     * Create Term functions                                        *
     ****************************************************************/

    // Create and return an ASTNode for a term
     inline BEEV::ASTNode CreateTerm(BEEV::Kind kind, unsigned int width, const BEEV::ASTVec &children =_empty_ASTVec)
     {
    	 return defaultNodeFactory->CreateTerm(kind,width,children);
     }

     inline BEEV::ASTNode CreateArrayTerm(BEEV::Kind kind, unsigned int indexWidth, unsigned int width, const BEEV::ASTVec &children =_empty_ASTVec)
     {
         return defaultNodeFactory->CreateArrayTerm(kind,indexWidth, width,children);
     }

     inline ASTNode CreateTerm(Kind kind, unsigned int width,
     		const ASTNode& child0, const ASTVec &children = _empty_ASTVec) {
     	return defaultNodeFactory->CreateTerm(kind, width, child0, children);
     }

     inline ASTNode CreateTerm(Kind kind, unsigned int width,
     		const ASTNode& child0, const ASTNode& child1, const ASTVec &children = _empty_ASTVec) {
     	return defaultNodeFactory->CreateTerm(kind,width, child0, child1,children);
     }

     inline ASTNode CreateTerm(Kind kind, unsigned int width,
     		const ASTNode& child0, const ASTNode& child1, const ASTNode& child2,
     		const ASTVec &children =  _empty_ASTVec) {
     	return defaultNodeFactory->CreateTerm(kind, width, child0, child1, child2);
     }


    /****************************************************************
     * Functions that manage logical context                        *
     ****************************************************************/

    void Pop(void);
    void Push(void);    
    const ASTNode PopQuery();
    const ASTNode GetQuery();
    const ASTVec GetAsserts();
    const ASTVec getVectorOfAsserts();


    //add a query/assertion to the current logical context
    void AddQuery(const ASTNode& q);
    void AddAssert(const ASTNode& assert);
    
    /****************************************************************
     * Toplevel printing and stats functions                        *
     ****************************************************************/

    // For printing purposes
    // Not filled in by the smtlib parser.
    ASTVec ListOfDeclaredVars;
    
    // Table for DAG printing.
    ASTNodeSet AlreadyPrintedSet;
    
    //Nodes seen so far
    ASTNodeSet PLPrintNodeSet;

    // Map from ASTNodes to LetVars
    ASTNodeMap NodeLetVarMap;

    // This is a vector which stores the Node to LetVars pairs. It
    // allows for sorted printing, as opposed to NodeLetVarMap
    std::vector<pair<ASTNode, ASTNode> > NodeLetVarVec;

    // A partial Map from ASTNodes to LetVars. Needed in order to
    // correctly print shared subterms inside the LET itself
    ASTNodeMap NodeLetVarMap1;

    //prints statistics for the ASTNode.
    void ASTNodeStats(const char * c, const ASTNode& a);

    // Print variable to the input stream
    void printVarDeclsToStream(ostream &os, ASTNodeSet& symbols);

    // Print assertions to the input stream
    void printAssertsToStream(ostream &os, int simplify);

    // Variables are added automatically to the introduced_symbolset. Variables
    // in the set aren't printed out as part of the counter example.
    ASTNode CreateFreshVariable(int indexWidth, int valueWidth, std::string prefix)
    {
        char d[32 + prefix.length()];
        sprintf(d, "%s_%d", prefix.c_str(), _symbol_count++);
        assert(!LookupSymbol(d));

        BEEV::ASTNode CurrentSymbol = CreateSymbol(d,indexWidth,valueWidth);
        Introduced_SymbolsSet.insert(CurrentSymbol);
        return CurrentSymbol;
    }

    bool FoundIntroducedSymbolSet(const ASTNode& in)
    {
      if(Introduced_SymbolsSet.find(in) != Introduced_SymbolsSet.end())
        {
          return true;
        }
      return false;
    } // End of IntroduceSymbolSet

    bool VarSeenInTerm(const ASTNode& var, const ASTNode& term);

    ASTNode NewParameterized_BooleanVar(const ASTNode& var,
                                        const ASTNode& constant);

    void TermsAlreadySeenMap_Clear(void)
    {
      TermsAlreadySeenMap.clear();
    }

    // This is called before SAT solving, so only junk that isn't needed
    // after SAT solving should be cleaned out.
    void ClearAllTables(void) 
    {
      NodeLetVarMap.clear();
      NodeLetVarMap1.clear();
      PLPrintNodeSet.clear();
      AlreadyPrintedSet.clear();
      TermsAlreadySeenMap.clear();
      NodeLetVarVec.clear();
      ListOfDeclaredVars.clear();
    } //End of ClearAllTables()

    ~STPMgr();

  };//End of Class STPMgr
};//end of namespace
#endif
