// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/

#ifndef LETMGR_H
#define LETMGR_H

#include "../AST/AST.h"

namespace BEEV
{

//LET Management
  class LETMgr 
  {
  private:

	  // Hash function for the hash_map of a string..
	template <class T>
	struct hashF {
				  size_t operator() (const T & x) const {
						  return __gnu_cxx::hash<const char*>()(x.c_str());
				  }
		  };

    const ASTNode ASTUndefined;

    typedef hash_map<string,ASTNode, hashF<std::string> > MapType;

    // MAP: This map is from bound IDs that occur in LETs to
    // expression. The map is useful in checking replacing the IDs
    // with the corresponding expressions. As soon as the brackets
    // that close a let expression is reached, it is emptied by
    // a call to CleanupLetIDMap().
    MapType *_letid_expr_map;

    //Allocate LetID map
    void InitializeLetIDMap(void);

 public:

    // I think this keeps a reference to symbols so they don't get garbage collected.
    ASTNodeSet _parser_symbol_table;

    // A let with this name has already been declared.
    bool isLetDeclared(string s)
    {
      return _letid_expr_map->find(s) !=_letid_expr_map->end();
    }

    void cleanupParserSymbolTable()
    {
    	_parser_symbol_table.clear();
    }

    LETMgr(ASTNode undefined)
    : ASTUndefined(undefined)
    {
    	assert(!undefined.IsNull());
    	InitializeLetIDMap();
    }

    ~LETMgr()
    {
      delete _letid_expr_map;
    }

    // We know for sure that it's a let.
    ASTNode resolveLet(const string s)
    {
      assert(isLetDeclared(s));
      return _letid_expr_map->find(s)->second;
    }

    ASTNode ResolveID(const ASTNode& var);
      
    //Functions that are used to manage LET expressions
    void LetExprMgr(const ASTNode& var, const ASTNode& letExpr);
    void LetExprMgr(string name, const ASTNode& letExpr);
      
    //Delete Letid Map. Called when we move onto the expression after (let ... )
    void CleanupLetIDMap(void);

  };// End of class LETMgr
}; //end of namespace

#endif
