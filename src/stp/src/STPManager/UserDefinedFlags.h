// -*- c++ -*-
/********************************************************************
 * AUTHORS: Vijay Ganesh
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
#ifndef UDEFFLAGS_H
#define UDEFFLAGS_H

#include <map>
#include <string>
#include <assert.h>
#include <iostream>
#include <set>
#include "../boost/noncopyable.hpp"

namespace BEEV
{
	using std::string;

  /******************************************************************
   * Struct UserDefFlags:
   *
   * Some userdefined variables that are set through commandline
   * options. 
   ******************************************************************/

  struct UserDefinedFlags : boost::noncopyable
  {
  private:
	std::set<string> alreadyOutput;

  public:
    //collect statistics on certain functions
    bool stats_flag;
    
    //print DAG nodes
    bool print_nodes_flag;
    
    //run STP in optimized mode
    bool optimize_flag;
    
    //do sat refinement, i.e. underconstrain the problem, and feed to
    //SAT. if this works, great. else, add a set of suitable constraints
    //to re-constraint the problem correctly, and call SAT again, until
    //all constraints have been added.
    bool ackermannisation; // eagerly write through the array's function congruence axioms.
    
    //switch to control write refinements
    //bool arraywrite_refinement_flag;
    
    //check the counterexample against the original input to STP
    bool check_counterexample_flag;
    
    //construct the counterexample in terms of original variable based
    //on the counterexample returned by SAT solver
    bool construct_counterexample_flag;
    bool print_counterexample_flag;
    bool print_binary_flag;
    
    //if this option is true then print the way dawson wants using a
    //different printer. do not use this printer.
    bool print_arrayval_declaredorder_flag;
    
    //Flag that determines whether the Boolean SAT solver should
    //assign random polarity to the Boolean variables
    bool random_seed_flag;
    int random_seed;

    //Flag that allows the printing of the DIMACS format of the input
    bool print_cnf_flag;
    char * cnf_dump_filename;

    //flag to decide whether to print "valid/invalid" or not
    bool print_output_flag;
    
    //print the variable order chosen by the sat solver while it is
    //solving.
    bool print_sat_varorder_flag;
    
    //turn on word level bitvector solver
    bool wordlevel_solve_flag;
    

    bool propagate_equalities;


    //XOR flattening optimizations.
    bool xor_flatten_flag;
    
    //this flag indicates that the BVSolver() succeeded
    bool toplevel_solved_flag;
  
    //print the input back
    bool print_STPinput_back_flag;
    bool print_STPinput_back_C_flag;
    bool print_STPinput_back_SMTLIB2_flag;
    bool print_STPinput_back_SMTLIB1_flag;
    bool print_STPinput_back_CVC_flag;
    bool print_STPinput_back_dot_flag;
    bool print_STPinput_back_GDL_flag;
    
    // output flags
    bool output_CNF_flag;
    bool output_bench_flag;

    //Flag to switch on the smtlib parser
    bool smtlib1_parser_flag;
    bool smtlib2_parser_flag;
    
    bool division_by_zero_returns_one_flag;
    
    bool quick_statistics_flag;
  
    bool tseitin_are_decision_variables_flag;

    // Create a new Tseitin variable for every intermediate value.
    bool renameAllInCNF_flag;

    bool bitConstantProp_flag;

    bool cBitP_propagateForDivisionByZero;

    bool exit_after_CNF;

    bool enable_AIG_rewrites_flag;

    bool simplify_during_BB_flag;

    // Available back-end SAT solvers.
    enum SATSolvers
      {
        MINISAT_SOLVER =0,
        SIMPLIFYING_MINISAT_SOLVER,
        CRYPTOMINISAT_SOLVER,
        MINISAT_PROPAGATORS
      };

    enum SATSolvers solver_to_use;

    std::map<string,string> config_options;

    void set(string n, string v)
    {
    	assert(n.size() > 0);
    	assert(v.size() > 0);
    	assert(config_options.find(n) == config_options.end());
    	config_options[n] = v;
    }

    void disableSimplifications()
    {
      optimize_flag = false;
      bitConstantProp_flag = false;
      set("enable-unconstrained","0");
      set("use-intervals","0");
      set("pure-literals","0");
      set("simple-cnf","1");
      set("always_true","0");
	   set("bitblast-simplification","0");

      wordlevel_solve_flag = false;
      propagate_equalities = false;
    }

    string get(string n)
    {
    	return get(n,"");
    }

    // "1" is set.
    bool isSet(string n, string def)
    {
    	return (get(n,def) == string("1"));
    }

    string get(string n, string def)
    {
    	if (config_options.empty())
    		return def;

    	string result;
    	std::map<string,string>::const_iterator it = config_options.find(n);
    	if (it == config_options.end())
    		result = def;
    	else
    		result = it->second;

    	if (stats_flag)
    		if (alreadyOutput.insert(n).second)
    			std::cout << "--config_"<< n << "="  << result << std::endl;
    	return result;
    }

    //CONSTRUCTOR    
    UserDefinedFlags()
    {  

    	//collect statistics on certain functions
      stats_flag = false;
      
      //print DAG nodes
      print_nodes_flag = false;
      
      //run STP in optimized mode
      optimize_flag = true;
      
      // Do sat refinement, i.e. underconstraint the problem, and feed to
      // SAT. if this works, great. else, add a set of suitable
      // constraints to re-constraint the problem correctly, and call SAT again, 
      // until all constraints have been added.
      ackermannisation = false;
  
      //flag to control write refinement
      //arraywrite_refinement_flag = true;
      
      //check the counterexample against the original input to STP
      check_counterexample_flag = true;
      
      //construct the counterexample in terms of original variable based
      //on the counterexample returned by SAT solver
      construct_counterexample_flag = true;
      print_counterexample_flag = false;
      print_binary_flag = false;
      
      output_CNF_flag = false;
      output_bench_flag = false;

      //if this option is true then print the way dawson wants using a
      //different printer. do not use this printer.
      print_arrayval_declaredorder_flag = false;
      
      //Flag that determines whether the Boolean SAT solver should
      //assign random polarity to the Boolean variables
      random_seed_flag = false;
      random_seed = 0;

      //flag to decide whether to print "valid/invalid" or not
      print_output_flag = false;
      
      //print the variable order chosen by the sat solver while it is
      //solving.
      print_sat_varorder_flag = false;
      
      //turn on word level bitvector solver
      wordlevel_solve_flag = true;
      
      //propagate equalities.
      propagate_equalities = true;

      //turn off XOR flattening
      xor_flatten_flag = false;
      
      //Flag to switch on the smtlib parser
      smtlib1_parser_flag = false;
      smtlib2_parser_flag = false;
      
      //print the input back
      print_STPinput_back_flag = false;
      print_STPinput_back_C_flag = false;
      print_STPinput_back_SMTLIB2_flag  = false;
      print_STPinput_back_SMTLIB1_flag = false;
      print_STPinput_back_CVC_flag  = false;
      print_STPinput_back_GDL_flag = false;
      print_STPinput_back_dot_flag = false;
      
      // If enabled. division, mod and remainder by zero will evaluate to
      // 1.
      division_by_zero_returns_one_flag = false;
      
      quick_statistics_flag=false;

      tseitin_are_decision_variables_flag=true;

      // use minisat by default.
      solver_to_use = MINISAT_PROPAGATORS;

      // The special Cryptominisat2 CNF generation with this flag enabled seems to go into an infinite loop.
      // beware of turning this on if you are using cryptominsat2.
      renameAllInCNF_flag= false;

      // Should constant bit propagation be enabled?
      bitConstantProp_flag = true;

      // given a/b = c, propagates that c<=a even if b may be zero.
      cBitP_propagateForDivisionByZero =true;

      exit_after_CNF=false;

      enable_AIG_rewrites_flag = false;

      // If the bit-blaster discovers new constants, should the term simplifier be re-run.
      simplify_during_BB_flag=false;

    } //End of constructor for UserDefinedFlags

  }; //End of struct UserDefinedFlags
};//end of namespace

#endif
