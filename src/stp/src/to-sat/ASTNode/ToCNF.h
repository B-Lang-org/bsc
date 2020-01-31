// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef TOCNF_H
#define TOCNF_H

#include <cmath>
#include <cassert>
#include "../../AST/AST.h"
#include "../../STPManager/STPManager.h"
#include "ClauseList.h"
#include "../../boost/noncopyable.hpp"

namespace BEEV
{
  class CNFMgr  : boost::noncopyable
  {  
  private:

    // Setting this to true changes the behaviour of when new
    // Tseitin variables are created.  Normally a Tseitin
    // variable is created only if: (the number of clauses is
    // >1) && (renaming of the node is enabled || the node is
    // shared). When this is set, every node is replaced by a
    // new tseitin variable.
    bool renameAllSiblings;

    //########################################
    //########################################
    // data types

    // for the meaning of control bits, see "utilities for contol
    // bits".
    struct CNFInfo
    {
      int control;
      ClauseList* clausespos;
      union
      {
        ClauseList* clausesneg;
        ASTNode* termforcnf;
      };

      CNFInfo()
      {
    	control = 0;
    	clausespos = NULL;
		clausesneg = NULL;
      }
    } ;

    //Collect all XOR Clauses here
    ClauseList* clausesxor;

    typedef HASHMAP<
      ASTNode, 
      CNFInfo*, 
      ASTNode::ASTNodeHasher, 
      ASTNode::ASTNodeEqual> ASTNodeToCNFInfoMap;

    typedef HASHMAP<
      ASTNode, 
      ASTNode*, 
      ASTNode::ASTNodeHasher, 
      ASTNode::ASTNodeEqual> ASTNodeToASTNodePtrMap;

    //########################################
    //########################################
    // this is the data

    STPMgr *bm;
    ASTNodeToCNFInfoMap info;
    ASTNodeToASTNodePtrMap store;
      
    //########################################
    //########################################
    // utility predicates

    bool onChildDoPos(const ASTNode& varphi, unsigned int idx);
    
    bool onChildDoNeg(const ASTNode& varphi, unsigned int idx);
    

    //########################################
    //########################################
    //utilities for control bits.

    void initializeCNFInfo(CNFInfo& x);    

    void incrementSharesPos(CNFInfo& x);    

    int sharesPos(CNFInfo& x);

    void incrementSharesNeg(CNFInfo& x);    

    int sharesNeg(CNFInfo& x);    

    void setControlBit(CNFInfo& x, unsigned int idx);    

    bool getControlBit(CNFInfo& x, unsigned int idx);    

    void setIsTerm(CNFInfo& x);    

    bool isTerm(CNFInfo& x);    

    void setDoRenamePos(CNFInfo& x);

    bool doRenamePos(CNFInfo& x);

    void setWasRenamedPos(CNFInfo& x);

    bool wasRenamedPos(CNFInfo& x);

    void setDoRenameNeg(CNFInfo& x);

    bool doRenameNeg(CNFInfo& x);

    void setWasRenamedNeg(CNFInfo& x);

    bool wasRenamedNeg(CNFInfo& x);

    void setDoSibRenamingPos(CNFInfo& x);    

    bool doSibRenamingPos(CNFInfo& x);    

    void setDoSibRenamingNeg(CNFInfo& x);    

    bool doSibRenamingNeg(CNFInfo& x);    

    void setWasVisited(CNFInfo& x);

    bool wasVisited(CNFInfo& x);    

    //########################################
    //########################################
    //utilities for clause sets


    ClauseList* SINGLETON(const ASTNode& varphi);    

    //########################################
    //########################################
    //prep. for cnf conversion

    void scanFormula(const ASTNode& varphi, bool isPos, bool isXorChild);    

    void scanTerm(const ASTNode& varphi);    

    //########################################
    //########################################
    // main cnf conversion function

    void convertFormulaToCNF(const ASTNode& varphi, ClauseList* defs);    

    void convertTermForCNF(const ASTNode& varphi, ClauseList* defs);    

    //########################################
    //########################################
    // functions for renaming nodes during cnf conversion

    ASTNode* doRenameITE(const ASTNode& varphi, ClauseList* defs);    

    void doRenamingPos(const ASTNode& varphi, ClauseList* defs);    

    void doRenamingPosXor(const ASTNode& varphi);    

    void doRenamingNegXor(const ASTNode& varphi);    

    void doRenamingNeg(const ASTNode& varphi, ClauseList* defs);    

    //########################################
    //########################################
    //main switch for individual cnf conversion cases

    void convertFormulaToCNFPosCases(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegCases(const ASTNode& varphi, ClauseList* defs);

    //########################################
    //########################################
    // individual cnf conversion cases

    void convertFormulaToCNFPosPred(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFPosFALSE(const ASTNode& varphi, ClauseList* defs);  
    void convertFormulaToCNFPosTRUE(const ASTNode& varphi, ClauseList* defs);   
    void convertFormulaToCNFPosBVGETBIT(const ASTNode& varphi, 
                                        ClauseList* defs);    
    void convertFormulaToCNFPosSYMBOL(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFPosNOT(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFPosAND(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFPosNAND(const ASTNode& varphi, ClauseList* defs);   
    void convertFormulaToCNFPosOR(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFPosNOR(const ASTNode& varphi, ClauseList* defs);   
    void convertFormulaToCNFPosIMPLIES(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFPosITE(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFPosXOR(const ASTNode& varphi, ClauseList* defs);    
    ClauseList* convertFormulaToCNFPosXORAux(const ASTNode& varphi, 
                                             unsigned int idx, 
                                             ClauseList* defs);    
    void convertFormulaToCNFNegPred(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegFALSE(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegTRUE(const ASTNode& varphi, ClauseList* defs);   
    void convertFormulaToCNFNegBVGETBIT(const ASTNode& varphi,
                                        ClauseList* defs);    
    void convertFormulaToCNFNegSYMBOL(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegNOT(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFNegAND(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFNegNAND(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegOR(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFNegNOR(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFNegIMPLIES(const ASTNode& varphi, ClauseList* defs);
    void convertFormulaToCNFNegITE(const ASTNode& varphi, ClauseList* defs);    
    void convertFormulaToCNFNegXOR(const ASTNode& varphi, ClauseList* defs);    
    ClauseList* convertFormulaToCNFNegXORAux(const ASTNode& varphi, 
                                             unsigned int idx, 
                                             ClauseList* defs);    

    //########################################
    //########################################
    // utilities for reclaiming memory.

    void reduceMemoryFootprintPos(const ASTNode& varphi);    
    void reduceMemoryFootprintNeg(const ASTNode& varphi);    

    //########################################
    //########################################

    ASTNode* ASTNodeToASTNodePtr(const ASTNode& varphi);    

    //########################################
    //########################################

    void cleanup(const ASTNode& varphi);    

    ASTNode dummy_true_var;

  public:

    //########################################
    //########################################
    // constructor
    CNFMgr(STPMgr *bmgr);
   
    //########################################
    //########################################
    // destructor
    ~CNFMgr();
    
    //########################################
    //########################################
    // top-level conversion function

    ClauseList* convertToCNF(const ASTNode& varphi);    

    ClauseList* ReturnXorClauses(void);

    // Destructors that need to be explicitly called...(yuck).
    // One deletes the thing passed into it.

    static void DELETE(ClauseList* varphi);

    //void PrintClauseList(ostream& os, ClauseList& cll);
  }; // end of CNFMgr class
};//end of namespace
#endif
