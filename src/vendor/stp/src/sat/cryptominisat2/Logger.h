/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef LOGGER_H
#define LOGGER_H

#include <stdio.h>
#include <set>
#include <vector>
#include <string>
#include <map>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "Vec.h"
#include "Heap.h"
#include "Alg.h"
#include "SolverTypes.h"
#include "limits.h"
#include "Clause.h"

using std::vector;
using std::pair;
using std::string;
using std::map;

namespace MINISAT
{
using namespace MINISAT;

class Solver;

class MyAvg {
public:
    MyAvg() :
        sum(0)
        , num(0)
        {}
    
    uint sum;
    uint num;
};

class Logger
{
public:
    Logger(int& vebosity);
    void setSolver(const Solver* S);

    //types of props, confl, and finish
    enum prop_type { add_clause_type, guess_type, simple_propagation_type};
    enum confl_type { simple_confl_type, gauss_confl_type };
    enum finish_type { model_found, unsat_model_found, restarting};

    //Conflict and propagation(guess is also a proapgation...)
    template<class T>
    void conflict(const confl_type type, const uint goback_level, const uint group, const T& learnt_clause);
    void propagation(const Lit lit, Clause* c);

    //functions to add/name variables
    void new_var(const Var var);
    void set_variable_name(const uint var, char* name_tmp);

    //function to name clause groups
    void set_group_name(const uint group, const char* name_tmp);
    void set_group_name(const uint group, string& name);
    string get_group_name(const uint group) const;
    string get_var_name(const Var var) const;

    void begin();
    void end(const finish_type finish);

    void newclause(const vec<Lit>& ps, const bool xor_clause, const uint group);

    bool proof_graph_on;
    bool mini_proof;
    bool statistics_on;
    
private:
    void new_group(const uint group);
    string cut_name_to_size(const string& name) const;
    
    void print_groups(const vector<pair<uint, uint> >& to_print) const;
    void print_groups(const vector<pair<double, uint> >& to_print) const;
    void print_vars(const vector<pair<uint, uint> >& to_print) const;
    void print_vars(const vector<pair<double, uint> >& to_print) const;
    void print_times_var_guessed() const;
    void print_times_group_caused_propagation() const;
    void print_times_group_caused_conflict() const;
    void print_branch_depth_distrib() const;
    void print_learnt_clause_distrib() const;
    void print_leearnt_clause_graph_distrib(const uint maximum, const map<uint, uint>& learnt_sizes) const;
    void print_advanced_stats() const;
    void print_statistics_note() const;
    void print_matrix_stats() const;
    void print_general_stats() const;
    void print_learnt_unitaries(const uint from, const string display) const;

    uint max_print_lines;
    template<class T>
    void print_line(const uint& number, const string& name, const T& value) const;
    void print_header(const string& first, const string& second, const string& third) const;
    void print_footer() const;
    template<class T>
    void print_line(const string& str, const T& num) const;
    void print_simple_line(const string& str) const;
    void print_center_line(const string& str) const;
    
    void print_confl_order() const;
    void print_prop_order() const;
    void print_assign_var_order() const;
    void printstats() const;
    void reset_statistics();

    //internal data structures
    uint uniqueid; //used to store the last unique ID given to a node
    vector<uint> history; //stores the node uniqueIDs

    //graph drawing
    FILE* proof; //The file to store the proof
    uint runid;

    //---------------------
    //statistics collection
    //---------------------

    //group and var names
    vector<string> groupnames;
    vector<string> varnames;

    //confls and props grouped by clause groups
    vector<uint> confls_by_group;
    vector<uint> props_by_group;

    //props and guesses grouped by vars
    vector<uint> times_var_guessed;
    vector<uint> times_var_propagated;

    vector<uint> times_group_caused_conflict;
    vector<uint> times_group_caused_propagation;

    vector<MyAvg> depths_of_propagations_for_group;
    vector<bool>  depths_of_propagations_unit;
    vector<MyAvg> depths_of_conflicts_for_group;
    vector<MyAvg> depths_of_assigns_for_var;
    vector<bool>  depths_of_assigns_unit;

    //the distribution of branch depths. first = depth, second = number of occurances
    vector<uint> branch_depth_distrib;

    uint64_t sum_conflict_depths;
    uint64_t no_conflicts;
    uint64_t no_decisions;
    uint64_t no_propagations;
    uint64_t sum_decisions_on_branches;
    uint64_t sum_propagations_on_branches;
    uint64_t last_unitary_learnt_clauses;

    //message display properties
    const int& verbosity;
    
    const Solver* S;
    
    void first_begin();
    bool begin_called;
    uint proofStarts;
};

}; //NAMESPACE MINISAT

#endif //LOGGER_H
