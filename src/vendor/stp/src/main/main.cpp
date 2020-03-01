
/********************************************************************
 * AUTHORS: Vijay Ganesh, Trevor Hansen
 *
 * BEGIN DATE: November, 2005
 *
 * LICENSE: Please view LICENSE file in the home dir of this Program
 ********************************************************************/
// -*- c++ -*-
#include "../AST/AST.h"
#include "../printer/AssortedPrinters.h"
#include "../printer/printers.h"
#include "../STPManager/STPManager.h"
#include "../STPManager/STP.h"
#include "../AST/NodeFactory/TypeChecker.h"
#include "../AST/NodeFactory/SimplifyingNodeFactory.h"
#include "../cpp_interface/cpp_interface.h"
#include <sys/time.h>
#include <memory>
#include "../extlib-abc/cnf_short.h"


#ifdef EXT_HASH_MAP
using namespace __gnu_cxx;
#endif
using namespace BEEV;

extern int smtparse(void*);
extern int smt2parse();
extern int cvcparse(void*);
extern int cvclex_destroy(void);
extern int smtlex_destroy(void);
extern int smt2lex_destroy(void);

namespace BEEV
{
  void setHardTimeout(int);
}

bool onePrintBack =false;


static string tolower(const char * name)
{
  string s(name);
  for (size_t i = 0; i < s.size(); ++i)
	s[i] = ::tolower(s[i]);
  return s;
}



// Amount of memory to ask for at beginning of main.
static const intptr_t INITIAL_MEMORY_PREALLOCATION_SIZE = 4000000;
/********************************************************************
 * MAIN FUNCTION:
 *
 * step 0. Parse the input into an ASTVec.
 * step 1. Do BV Rewrites
 * step 2. Bitblasts the ASTNode.
 * step 3. Convert to CNF
 * step 4. Convert to SAT
 * step 5. Call SAT to determine if input is SAT or UNSAT
 ********************************************************************/

typedef enum {PRINT_BACK_C=1, PRINT_BACK_CVC, PRINT_BACK_SMTLIB2,PRINT_BACK_SMTLIB1, PRINT_BACK_GDL, PRINT_BACK_DOT, OUTPUT_BENCH, OUTPUT_CNF, USE_SIMPLIFYING_SOLVER, SMT_LIB2_FORMAT, SMT_LIB1_FORMAT, DISABLE_CBITP,EXIT_AFTER_CNF,USE_CRYPTOMINISAT_SOLVER,USE_MINISAT_SOLVER, DISABLE_SIMPLIFICATIONS, OLDSTYLE_REFINEMENT, DISABLE_EQUALITY, RANDOM_SEED,HASHING_NF} OptionType;


int main(int argc, char ** argv) {
  char * infile = NULL;
  extern FILE *cvcin;
  extern FILE *smtin;
  extern FILE *smt2in;

  // Grab some memory from the OS upfront to reduce system time when
  // individual hash tables are being allocated
  if (sbrk(INITIAL_MEMORY_PREALLOCATION_SIZE) == ((void *) -1))
    {
      FatalError("Initial allocation of memory failed.");
    }


  STPMgr * bm       = new STPMgr();

  auto_ptr<SimplifyingNodeFactory> simplifyingNF( new SimplifyingNodeFactory(*bm->hashingNodeFactory, *bm));
  bm->defaultNodeFactory = simplifyingNF.get();

  // The simplified keeps a pointer to whatever is set as the default node factory.
  Simplifier * simp  = new Simplifier(bm);
  auto_ptr<Simplifier> simpCleaner(simp);

  ArrayTransformer * arrayTransformer = new ArrayTransformer(bm, simp);
  auto_ptr<ArrayTransformer> atClearner(arrayTransformer);

  ToSAT * tosat      = new ToSAT(bm);
  auto_ptr<ToSAT> tosatCleaner(tosat);

  AbsRefine_CounterExample * Ctr_Example = new AbsRefine_CounterExample(bm, simp, arrayTransformer);
  auto_ptr<AbsRefine_CounterExample> ctrCleaner(Ctr_Example);

  ParserBM          = bm;
  GlobalSTP         = 
    new STP(bm, 
            simp, 
            arrayTransformer, 
            tosat, 
            Ctr_Example);
  

  //populate the help string
  helpstring += 
    "STP version            : " + version + "\n"
    "--disable-simplify     : disable all simplifications\n"
    "-w                     : switch wordlevel solver off (optimizations are ON by default)\n"
    "-a                     : disable potentially size-increasing optimisations\n"
    "--disable-cbitp        : disable constant bit propagation\n"
    "--disable-equality     : disable equality propagation\n"
    "\n"
    "--cryptominisat        : use cryptominisat2 as the solver\n"
    "--simplifying-minisat  : use simplifying-minisat 2.2 as the solver\n"
    "--minisat              : use minisat 2.2 as the solver\n"
    "\n"
    "--oldstyle-refinement  : Do abstraction-refinement outside the SAT solver\n"
    "-r                     : Eagerly encode array-read axioms (Ackermannistaion)\n"
    "\n"
    "-b                     : print STP input back to cout\n"
    "--print-back-CVC       : print input in CVC format, then exit\n"
    "--print-back-SMTLIB2   : print input in SMT-LIB2 format, then exit\n"
    "--print-back-SMTLIB1   : print input in SMT-LIB1 format, then exit\n"
    "--print-back-GDL       : print AiSee's graph format, then exit\n"
    "--print-back-dot       : print dotty/neato's graph format, then exit\n"
    "\n"
    "--SMTLIB1 -m           : use the SMT-LIB1 format parser\n"
    "--SMTLIB2              : use the SMT-LIB2 format parser\n"
    "\n"
    "--output-CNF           : save the CNF into output_[0..n].cnf\n"
    "--output-bench         : save in ABC's bench format to output.bench\n"
    "\n"
    "--exit-after-CNF       : exit after the CNF has been generated\n"
    "-g <time_in_sec>       : timeout (seconds until STP gives up)\n"
    "-h                     : help\n"
    "-i <random_seed>       : Randomize STP's satisfiable output. Random_seed is an integer >= 0\n"
    "--random-seed          : Generate a random number for the SAT solver.\n"
    "-p                     : print counterexample\n"
    "-s                     : print function statistics\n"
    "-t                     : print quick statistics\n"
    "-v                     : print nodes \n"
    "-y                     : print counterexample in binary\n";

    //  "-x                     : flatten nested XORs\n"
    //  "-c                     : construct counterexample\n"
    //   "-d                     : check counterexample\n"

  for(int i=1; i < argc;i++)
    {
      if(argv[i][0] == '-')
        {
    	  if(argv[i][1] == '-')
    	  {
    		  // long options.
    		  map<string,OptionType> lookup;
    		  lookup.insert(make_pair(tolower("--print-back-C"),PRINT_BACK_C));
    		  lookup.insert(make_pair(tolower("--cryptominisat"),USE_CRYPTOMINISAT_SOLVER));
    		lookup.insert(make_pair(tolower("--minisat"),USE_MINISAT_SOLVER));

                          lookup.insert(make_pair(tolower("--print-back-CVC"),PRINT_BACK_CVC));
			  lookup.insert(make_pair(tolower("--print-back-SMTLIB2"),PRINT_BACK_SMTLIB2));
			  lookup.insert(make_pair(tolower("--print-back-SMTLIB1"),PRINT_BACK_SMTLIB1));
			  lookup.insert(make_pair(tolower("--print-back-GDL"),PRINT_BACK_GDL));
			  lookup.insert(make_pair(tolower("--print-back-dot"),PRINT_BACK_DOT));
			  lookup.insert(make_pair(tolower("--output-CNF"),OUTPUT_CNF));
                          lookup.insert(make_pair(tolower("--exit-after-CNF"),EXIT_AFTER_CNF));
			  lookup.insert(make_pair(tolower("--output-bench"),OUTPUT_BENCH));
			  lookup.insert(make_pair(tolower("--simplifying-minisat"),USE_SIMPLIFYING_SOLVER));
			  lookup.insert(make_pair(tolower("--SMTLIB2"),SMT_LIB2_FORMAT));
			  lookup.insert(make_pair(tolower("--SMTLIB1"),SMT_LIB1_FORMAT));
			  lookup.insert(make_pair(tolower("--disable-cbitp"),DISABLE_CBITP));
			  lookup.insert(make_pair(tolower("--disable-simplify"),DISABLE_SIMPLIFICATIONS));
			  lookup.insert(make_pair(tolower("--oldstyle-refinement"),OLDSTYLE_REFINEMENT));
			  lookup.insert(make_pair(tolower("--disable-equality"),DISABLE_EQUALITY));
			  lookup.insert(make_pair(tolower("--random-seed"),RANDOM_SEED));
			  lookup.insert(make_pair(tolower("--hash-nf"),HASHING_NF));


			  if (!strncmp(argv[i],"--config_",strlen("--config_")))
			  {
				  // Must contain an equals.
				  // Must contain a name >=1 character long.
				  // Must contain a value >=1 char.
				  string s(argv[i]);
				  size_t a = s.find("_");
				  size_t b = s.find("=");
				  if (a== string::npos || b == string::npos || b < a || b==a+1 || b==s.length()-1)
				  {
					   fprintf(stderr,usage,prog);
		               cout << helpstring;
		               return -1;
		               break;
				  }

				  string name = s.substr(a+1,b-a-1);
				  string value = s.substr(b+1);

				  bm->UserFlags.set(name,value);
			  }
			  else

			  switch(lookup[tolower(argv[i])])
			  {
			  case DISABLE_CBITP:
                                  bm->UserFlags.bitConstantProp_flag = false;
                                  break;
			  case EXIT_AFTER_CNF:
                                  bm->UserFlags.exit_after_CNF = true;
                                  break;
			  case PRINT_BACK_C:
				  bm->UserFlags.print_STPinput_back_C_flag = true;
				  onePrintBack = true;
				  break;
			  case PRINT_BACK_CVC:
				  bm->UserFlags.print_STPinput_back_CVC_flag = true;
				  onePrintBack = true;
				  break;
			  case PRINT_BACK_SMTLIB2:
				  bm->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
				  onePrintBack = true;
				  break;
			  case PRINT_BACK_SMTLIB1:
				  bm->UserFlags.print_STPinput_back_SMTLIB1_flag = true;
				  onePrintBack = true;
				  break;
			  case PRINT_BACK_GDL:
				  bm->UserFlags.print_STPinput_back_GDL_flag = true;
				  onePrintBack = true;
				  break;
			  case PRINT_BACK_DOT:
				  bm->UserFlags.print_STPinput_back_dot_flag = true;
				  onePrintBack = true;
				  break;
			  case OUTPUT_CNF:
				  bm->UserFlags.output_CNF_flag = true;
				  //bm->UserFlags.print_cnf_flag = true;
				  break;
			  case OUTPUT_BENCH:
				  bm->UserFlags.output_bench_flag = true;
				  break;
			  case SMT_LIB2_FORMAT:
				  bm->UserFlags.smtlib2_parser_flag = true;
				  bm->UserFlags.division_by_zero_returns_one_flag = true;
				  if (bm->UserFlags.smtlib1_parser_flag)
					  FatalError("Can't use both the smtlib and smtlib2 parsers");
				  break;
			  case SMT_LIB1_FORMAT:
				  bm->UserFlags.smtlib1_parser_flag = true;
				  bm->UserFlags.division_by_zero_returns_one_flag = true;
				  if (bm->UserFlags.smtlib2_parser_flag)
					  FatalError("Can't use both the smtlib and smtlib2 parsers");
				  break;
			  case USE_SIMPLIFYING_SOLVER:
				  bm->UserFlags.solver_to_use = UserDefinedFlags::SIMPLIFYING_MINISAT_SOLVER;
				  break;
                          case USE_CRYPTOMINISAT_SOLVER:
                                  bm->UserFlags.solver_to_use = UserDefinedFlags::CRYPTOMINISAT_SOLVER;
                                  break;
                          case USE_MINISAT_SOLVER:
                                  bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
                                  break;
                          case OLDSTYLE_REFINEMENT:
                                  bm->UserFlags.solver_to_use = UserDefinedFlags::MINISAT_SOLVER;
                                  break;
                          case DISABLE_SIMPLIFICATIONS:
                                  bm->UserFlags.disableSimplifications();
                                break;
                          case DISABLE_EQUALITY:
                                  bm->UserFlags.propagate_equalities = false;
                                  break;
                          case RANDOM_SEED:
                            {
                                srand(time(NULL));
                                bm->UserFlags.random_seed_flag = true;
                                bm->UserFlags.random_seed = rand();
                            }
                            break;
                          case HASHING_NF:
                              bm->defaultNodeFactory = bm->hashingNodeFactory;
                              break;

			  default:
				  fprintf(stderr,usage,prog);
	               cout << helpstring;
	               return -1;
	               break;
			  }
    	  }
      else
      {
    	  if(argv[i][2])
            {
              fprintf(stderr, 
                      "Multiple character options are not allowed.\n");
              fprintf(stderr, 
                      "(for example: -ab is not an abbreviation for -a -b)\n");
              fprintf(stderr,usage,prog);
              cout << helpstring;
              return -1;
            }

      if (argv[i][1] == 'g')
        {
        BEEV::setHardTimeout(atoi(argv[++i]));
        }
      else if (argv[i][1] == 'i')
        {
        bm->UserFlags.random_seed_flag = true;
        bm->UserFlags.random_seed = atoi(argv[++i]);
        //cerr << "Random seed is: " << bm->UserFlags.random_seed << endl;
        if(!(0 <= bm->UserFlags.random_seed))
          {
            FatalError("Random Seed should be an integer >= 0\n");
          }
        }
      else if (argv[i][1] == 'b')
        {
          onePrintBack = true;
          bm->UserFlags.print_STPinput_back_flag = true;
        }
      else
    	  process_argument(argv[i][1],bm);

        }
        } else {          
        	if (NULL != infile)
				FatalError("One input file only.");
        	infile = argv[i];
      }
    }

  if (!bm->UserFlags.smtlib1_parser_flag &&  !bm->UserFlags.smtlib2_parser_flag)
  {
	  // No parser is explicity requested.
	  if (NULL != infile && strlen(infile)>=5)
	  {
		  string f(infile);
		  if (!f.compare(f.length()-4, 4,".smt"))
		  {
			  bm->UserFlags.division_by_zero_returns_one_flag = true;
			  bm->UserFlags.smtlib1_parser_flag = true;
		  }
		  if (!f.compare(f.length()-5, 5,".smt2"))
		  {
			  bm->UserFlags.division_by_zero_returns_one_flag = true;
			  bm->UserFlags.smtlib2_parser_flag = true;
		  }
	  }
  }

  FILE* toClose= 0;

  // If we're not reading the file from stdin.
  if (infile != NULL)
  {
  if (bm->UserFlags.smtlib1_parser_flag)
    {
      smtin = fopen(infile,"r");
      toClose = smtin;
      if(smtin == NULL)
        {
          fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
          FatalError("");
        }
    } else
        if (bm->UserFlags.smtlib2_parser_flag)
          {
            smt2in = fopen(infile,"r");
            toClose = smt2in;
            if(smt2in == NULL)
              {
                fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
                FatalError("");
              }
          }

  else
    {
      cvcin = fopen(infile,"r");
      toClose = cvcin;
      if(cvcin == NULL)
        {
          fprintf(stderr,"%s: Error: cannot open %s\n",prog,infile);
          FatalError("");
        }
    }
  }


  //want to print the output always from the commandline.
  bm->UserFlags.print_output_flag = true;
  ASTVec * AssertsQuery = new ASTVec;

  bm->GetRunTimes()->start(RunTimes::Parsing);
	{
                TypeChecker nfTypeCheckSimp(*bm->defaultNodeFactory, *bm);
		TypeChecker nfTypeCheckDefault(*bm->hashingNodeFactory, *bm);

		Cpp_interface piTypeCheckSimp(*bm, &nfTypeCheckSimp);
		Cpp_interface piTypeCheckDefault(*bm, &nfTypeCheckDefault);

		// If you are converting formats, you probably don't want it simplifying (at least I dont).
		if (onePrintBack)
		{
			parserInterface = &piTypeCheckDefault;
		}
		else
			parserInterface = &piTypeCheckSimp;

		  parserInterface->startup();

		if (onePrintBack)
		  {
		    if (bm->UserFlags.smtlib2_parser_flag)
		      {
		        cerr << "Printback from SMTLIB2 inputs isn't currently working." << endl;
		        cerr << "Please try again later" << endl;
		        cerr << "It works prior to revision 1354" << endl;
		        exit(1);
		      }
		  }


		if (bm->UserFlags.smtlib1_parser_flag) {
			smtparse((void*) AssertsQuery);
			smtlex_destroy();
		} else if (bm->UserFlags.smtlib2_parser_flag) {
		        smt2parse();
			smt2lex_destroy();
		} else {
			cvcparse((void*) AssertsQuery);
			cvclex_destroy();
		}
		parserInterface = NULL;
		if (toClose != NULL)
			fclose(toClose);
	}
	bm->GetRunTimes()->stop(RunTimes::Parsing);

  /*  The SMTLIB2 has a command language. The parser calls all the functions,
   *  so when we get to here the parser has already called "exit". i.e. if the
   *  language is smt2 then all the work has already been done, and all we need
   *  to do is cleanup...
   *    */
  if (!bm->UserFlags.smtlib2_parser_flag)
    {

      if (((ASTVec*) AssertsQuery)->empty())
        {
          FatalError("Input is Empty. Please enter some asserts and query\n");
        }

      if (((ASTVec*) AssertsQuery)->size() != 2)
        {
          FatalError("Input must contain a query\n");
        }

      ASTNode asserts = (*(ASTVec*) AssertsQuery)[0];
      ASTNode query = (*(ASTVec*) AssertsQuery)[1];

      if (onePrintBack)
        {

          ASTNode original_input = bm->CreateNode(AND, bm->CreateNode(NOT, query), asserts);

          if (bm->UserFlags.print_STPinput_back_flag)
            {
              if (bm->UserFlags.smtlib1_parser_flag)
                bm->UserFlags.print_STPinput_back_SMTLIB2_flag = true;
              else
                bm->UserFlags.print_STPinput_back_CVC_flag = true;
            }

          if (bm->UserFlags.print_STPinput_back_CVC_flag)
            {
              //needs just the query. Reads the asserts out of the data structure.
              print_STPInput_Back(original_input);
            }

          if (bm->UserFlags.print_STPinput_back_SMTLIB1_flag)
            {
              printer::SMTLIB1_PrintBack(cout, original_input);
            }

          if (bm->UserFlags.print_STPinput_back_SMTLIB2_flag)
            {
              printer::SMTLIB2_PrintBack(cout, original_input);
            }

          if (bm->UserFlags.print_STPinput_back_C_flag)
            {
              printer::C_Print(cout, original_input);
            }

          if (bm->UserFlags.print_STPinput_back_GDL_flag)
            {
              printer::GDL_Print(cout, original_input);
            }

          if (bm->UserFlags.print_STPinput_back_dot_flag)
            {
              printer::Dot_Print(cout, original_input);
            }

          return 0;
        }

      SOLVER_RETURN_TYPE ret = GlobalSTP->TopLevelSTP(asserts, query);
      if (bm->UserFlags.quick_statistics_flag)
        {
          bm->GetRunTimes()->print();
        }
      (GlobalSTP->tosat)->PrintOutput(ret);

      asserts = ASTNode();
      query = ASTNode();
    }

  // Currently for testcase12.stp.smt2 we spend 3 seconds running the destructors,
  // the total runtime is 17 seconds, so about 20% of runtime is spent destructing
  // which is wasted work because the process is going to be killed anyway.
  if (bm->UserFlags.isSet("fast-exit", "1"))
	  exit(0);

  AssertsQuery->clear();
  delete AssertsQuery;

  _empty_ASTVec.clear();

  simpCleaner.release();
  atClearner.release();
  tosatCleaner.release();
  ctrCleaner.release();

  delete GlobalSTP;
  delete ParserBM;

  Cnf_ClearMemory();

  return 0;
}//end of Main
