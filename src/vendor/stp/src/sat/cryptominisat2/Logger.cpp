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

#include <time.h>
#include <cstring>
#include <algorithm>
#include <vector>
#include <iostream>
#include <iomanip>
#include <fstream>
#include <sstream>
#include <limits>
using std::cout;
using std::endl;
using std::ofstream;

#include "Logger.h"
#include "SolverTypes.h"
#include "Solver.h"
#include "Gaussian.h"

#define FST_WIDTH 10
#define SND_WIDTH 35
#define TRD_WIDTH 10

namespace MINISAT
{
using namespace MINISAT;

Logger::Logger(int& _verbosity) :
    proof_graph_on(false)
    , mini_proof(false)
    , statistics_on(false)

    , max_print_lines(20)
    , uniqueid(1)

    , proof(NULL)

    , sum_conflict_depths(0)
    , no_conflicts(0)
    , no_decisions(0)
    , no_propagations(0)
    , sum_decisions_on_branches(0)
    , sum_propagations_on_branches(0)

    , verbosity(_verbosity)
    , begin_called(false)
    , proofStarts(0)
{
    runid /= 10;
    runid = time(NULL) % 10000;
    if (verbosity >= 1) printf("c RunID is: #%d\n",runid);
}

void Logger::setSolver(const Solver* _s)
{
    S = _s;
}

// Adds a new variable to the knowledge of the logger
void Logger::new_var(const Var var)
{
    if (!statistics_on && !proof_graph_on)
        return;

    if (varnames.size() <= var) {
        varnames.resize(var+1, "Noname");
        times_var_propagated.resize(var+1, 0);
        times_var_guessed.resize(var+1, 0);
        depths_of_assigns_for_var.resize(var+1);
        depths_of_assigns_unit.resize(var+1, false);
    }
}

// Resizes the groupnames and other, related vectors to accomodate for a new group
void Logger::new_group(const uint group)
{
    if (groupnames.size() <= group) {
        groupnames.resize(group+1, "Noname");
        times_group_caused_conflict.resize(group+1, 0);
        times_group_caused_propagation.resize(group+1, 0);
        depths_of_propagations_for_group.resize(group+1);
        depths_of_propagations_unit.resize(group+1, false);
        depths_of_conflicts_for_group.resize(group+1);
    }
}

string Logger::cut_name_to_size(const string& name) const
{
    string ret = name;
    uint len = name.length();
    while(len > 0 && (name[len-1] == ' ' || name[len-1] == 0x0A || name[len-1] == 0x0D)) {
        ret.resize(len-1);
        len--;
    }
    
    if (len > SND_WIDTH-3) {
        ret[SND_WIDTH-3] = '\0';
        ret[SND_WIDTH-4] = '.';
        ret[SND_WIDTH-5] = '.';
    }

    return ret;
}

// Adds the new clause group's name to the information stored
void Logger::set_group_name(const uint group, const char* name_tmp)
{
    if (!statistics_on && !proof_graph_on)
        return;
    
    string name;
    if (name_tmp == NULL) return;
    else name = name_tmp;

    set_group_name(group, name);
}

void Logger::set_group_name(const uint group, string& name)
{
    new_group(group);

    if (name == "Noname") return;

    if (groupnames[group] == "Noname") {
        groupnames[group] = name;
    } else if (groupnames[group] != name) {
        std::cout << "Error! Group no. " <<  group << "has been named twice. First, as '" << groupnames[group] << "', then second as '" <<  name << "'. Name the same group the same always, or don't give a name to the second iteration of the same group (i.e just write 'c g groupnumber' on the line" << std::endl;
        exit(-1);
    }
}

string Logger::get_group_name(const uint group) const
{
    assert(group < groupnames.size());
    return groupnames[group];
}

string Logger::get_var_name(const Var var) const
{
    if (var >= varnames.size()) return "unknown";
    return varnames[var];
}

// sets the variable's name
void Logger::set_variable_name(const uint var, char* name_tmp)
{
    if (!statistics_on && !proof_graph_on)
        return;
    
    new_var(var);
    
    string name;
    if (name_tmp == NULL)
        name = "";
    else
        name = name_tmp;
    
    if (varnames[var] == "Noname") {
        varnames[var] = name;
    } else if (varnames[var] != name) {
        printf("Error! Variable no. %d has been named twice. First, as '%s', then second as '%s'. Name the same group the same always, or don't give a name to the second iteration of the same group (i.e just write 'c g groupnumber' on the line\n", var+1, varnames[var].c_str(), name.c_str());
        exit(-1);
    }
}

void Logger::first_begin()
{
    if (begin_called)
        return;
    
    begin();
}

void Logger::begin()
{
    begin_called = true;
    if (proof_graph_on) {
        std::stringstream filename;
        filename << "proofs/" << runid << "-proof" << proofStarts++ << "-" << S->starts << ".dot";
        
        if (S->starts == 0)
            history.push_back(uniqueid);
        else {
            if (mini_proof)
                history.resize(S->decisionLevel()+1);
            else
                history.resize(S->trail.size()+1);
        }

        proof = fopen(filename.str().c_str(),"w");
        if (!proof) printf("Couldn't open proof file '%s' for writing\n", filename.str().c_str()), exit(-1);
        fprintf(proof, "digraph G {\n");
        fprintf(proof,"node%d [shape=circle, label=\"BEGIN\", root];\n", history[history.size()-1]);
    }

    if (statistics_on)
        reset_statistics();
}

// For noting conflicts. Updates the proof graph and the statistics.
template<class T>
void Logger::conflict(const confl_type type, const uint goback_level, const uint group, const T& learnt_clause)
{
    first_begin();
    assert(!(proof == NULL && proof_graph_on));
    
    const uint goback_sublevel = S->trail_lim[goback_level];

    if (proof_graph_on) {
        uniqueid++;
        fprintf(proof,"node%d [shape=polygon,sides=5,label=\"",uniqueid);
        
        if (!mini_proof) {
            for (uint32_t i = 0; i != learnt_clause.size(); i++) {
                if (learnt_clause[i].sign()) fprintf(proof,"-");
                int myvar = learnt_clause[i].var();
                if (varnames[myvar] != "Noname")
                    fprintf(proof,"%s\\n",varnames[myvar].c_str());
                else
                    fprintf(proof,"Var: %d\\n",myvar);
            }
        }
        fprintf(proof,"\"];\n");

        fprintf(proof,"node%d -> node%d [label=\"",history[history.size()-1],uniqueid);
        if (type == gauss_confl_type)
            fprintf(proof,"Gauss\",style=bold");
        else
            fprintf(proof,"%s\"", groupnames[group].c_str());
        fprintf(proof,"];\n");
        
        if (!mini_proof)
            history.resize(goback_sublevel+1);
        else
            history.resize(goback_level+1);
        fprintf(proof,"node%d -> node%d [style=dotted];\n",uniqueid,history[history.size()-1]);
    }

    if (statistics_on) {
        times_group_caused_conflict[group]++;
        depths_of_conflicts_for_group[group].sum += S->decisionLevel();
        depths_of_conflicts_for_group[group].num ++;
        
        no_conflicts++;
        sum_conflict_depths += S->trail.size() - S->trail_lim[0];
        sum_decisions_on_branches += S->decisionLevel();
        sum_propagations_on_branches += S->trail.size() - S->trail_lim[0] - S->decisionLevel();
        
        if (branch_depth_distrib.size() <= S->decisionLevel())
            branch_depth_distrib.resize(S->decisionLevel()+1, 0);
        branch_depth_distrib[S->decisionLevel()]++;
    }
}

template void Logger::conflict(const confl_type type, const uint goback_level, const uint group, const Clause& learnt_clause);

template void Logger::conflict(const confl_type type, const uint goback_level, const uint group, const vec<Lit>& learnt_clause);

// Propagating a literal. Type of literal and the (learned clause's)/(propagating clause's)/(etc) group must be given. Updates the proof graph and the statistics. note: the meaning of the variable 'group' depends on the type
void Logger::propagation(const Lit lit, Clause* c)
{
    first_begin();
    assert(!(proof == NULL && proof_graph_on));
    
    uint group;
    prop_type type;
    if (c == NULL) {
        if (S->decisionLevel() == 0)
            type = add_clause_type;
        else
            type = guess_type;
        group = std::numeric_limits<uint>::max();
    } else {
        type = simple_propagation_type;
        group = c->getGroup();
    }

    //graph
    if (proof_graph_on && (!mini_proof || type == guess_type)) {
        uniqueid++;
        
        fprintf(proof,"node%d [shape=box, label=\"",uniqueid);;
        if (lit.sign())
            fprintf(proof,"-");
        if (varnames[lit.var()] != "Noname")
            fprintf(proof,"%s\"];\n",varnames[lit.var()].c_str());
        else
            fprintf(proof,"Var: %d\"];\n",lit.var());

        fprintf(proof,"node%d -> node%d [label=\"",history[history.size()-1],uniqueid);
        
        switch (type) {
        case simple_propagation_type:
            fprintf(proof,"%s\"];\n", groupnames[group].c_str());
            break;
            
        case add_clause_type:
            fprintf(proof,"red. from clause\"];\n");
            break;
            
        case guess_type:
            fprintf(proof,"guess\",style=bold];\n");
            break;
        }
        history.push_back(uniqueid);
    }

    if (statistics_on) {
        switch (type) {
        case simple_propagation_type:
            depths_of_propagations_for_group[group].sum += S->decisionLevel();
            depths_of_propagations_for_group[group].num ++;
            if (S->decisionLevel() == 0) depths_of_propagations_unit[group] = true;
            times_group_caused_propagation[group]++;
        case add_clause_type:
            no_propagations++;
            times_var_propagated[lit.var()]++;
            depths_of_assigns_for_var[lit.var()].sum += S->decisionLevel();
            depths_of_assigns_for_var[lit.var()].num ++;
            if (S->decisionLevel() == 0) depths_of_assigns_unit[lit.var()] = true;
            break;
        case guess_type:
            no_decisions++;
            times_var_guessed[lit.var()]++;
            
            depths_of_assigns_for_var[lit.var()].sum += S->decisionLevel();
            depths_of_assigns_for_var[lit.var()].num ++;
            break;
        }
    }
}

// Ending of a restart iteration
void Logger::end(const finish_type finish)
{
    first_begin();
    assert(!(proof == NULL && proof_graph_on));
    
    if (proof_graph_on) {
        uniqueid++;
        switch (finish) {
        case model_found:
            fprintf(proof,"node%d [shape=doublecircle, label=\"MODEL\"];\n",uniqueid);
            break;
        case unsat_model_found:
            fprintf(proof,"node%d [shape=doublecircle, label=\"UNSAT\"];\n",uniqueid);
            break;
        case restarting:
            fprintf(proof,"node%d [shape=doublecircle, label=\"Re-starting\\nsearch\"];\n",uniqueid);
            break;
        }

        fprintf(proof,"node%d -> node%d;\n",history[history.size()-1],uniqueid);
        fprintf(proof,"}\n");
        history.push_back(uniqueid);

        proof = (FILE*)fclose(proof);
        assert(proof == NULL);
    }

    if (statistics_on) {
        printstats();
        if (finish == restarting)
            reset_statistics();
    }
    
    if (model_found || unsat_model_found)
        begin_called = false;
}

void Logger::print_footer() const
{
    cout << "+" << std::setfill('-') << std::setw(FST_WIDTH+SND_WIDTH+TRD_WIDTH+4) << "-" << std::setfill(' ') << "+" << endl;
}

void Logger::print_assign_var_order() const
{
    vector<pair<double, uint> > prop_ordered;
    for (uint i = 0; i < depths_of_assigns_for_var.size(); i++) {
        double avg = (double)depths_of_assigns_for_var[i].sum
                    /(double)depths_of_assigns_for_var[i].num;
        if (depths_of_assigns_for_var[i].num > 0 && !depths_of_assigns_unit[i])
            prop_ordered.push_back(std::make_pair(avg, i));
    }

    if (!prop_ordered.empty()) {
        print_footer();
        print_simple_line(" Variables are assigned in the following order");
        print_simple_line(" (unitary clauses not shown)");
        print_header("var", "var name", "avg order");
        std::sort(prop_ordered.begin(), prop_ordered.end());
        print_vars(prop_ordered);
    }
}

void Logger::print_prop_order() const
{
    vector<pair<double, uint> > prop_ordered;
    for (uint i = 0; i < depths_of_propagations_for_group.size(); i++) {
        double avg = (double)depths_of_propagations_for_group[i].sum
                    /(double)depths_of_propagations_for_group[i].num;
        if (depths_of_propagations_for_group[i].num > 0 && !depths_of_propagations_unit[i])
            prop_ordered.push_back(std::make_pair(avg, i));
    }

    if (!prop_ordered.empty()) {
        print_footer();
        print_simple_line(" Propagation depth order of clause groups");
        print_simple_line(" (unitary clauses not shown)");
        print_header("group", "group name", "avg order");
        std::sort(prop_ordered.begin(), prop_ordered.end());
        print_groups(prop_ordered);
    }
}

void Logger::print_confl_order() const
{
    vector<pair<double, uint> > confl_ordered;
    for (uint i = 0; i < depths_of_conflicts_for_group.size(); i++) {
        double avg = (double)depths_of_conflicts_for_group[i].sum
                    /(double)depths_of_conflicts_for_group[i].num;
        if (depths_of_conflicts_for_group[i].num > 0)
            confl_ordered.push_back(std::make_pair(avg, i));
    }

    if (!confl_ordered.empty()) {
        print_footer();
        print_simple_line(" Avg. conflict depth order of clause groups");
        print_header("groupno", "group name", "avg. depth");
        std::sort(confl_ordered.begin(), confl_ordered.end());
        print_groups(confl_ordered);
    }
}


void Logger::print_times_var_guessed() const
{
    vector<pair<uint, uint> > times_var_ordered;
    for (uint32_t i = 0; i != varnames.size(); i++) if (times_var_guessed[i] > 0)
            times_var_ordered.push_back(std::make_pair(times_var_guessed[i], i));

    if (!times_var_ordered.empty()) {
        print_footer();
        print_simple_line(" No. times variable branched on");
        print_header("var", "var name", "no. times");
        std::sort(times_var_ordered.rbegin(), times_var_ordered.rend());
        print_vars(times_var_ordered);
    }
}

void Logger::print_times_group_caused_propagation() const
{
    vector<pair<uint, uint> > props_group_ordered;
    for (uint i = 0; i < times_group_caused_propagation.size(); i++)
        if (times_group_caused_propagation[i] > 0)
            props_group_ordered.push_back(std::make_pair(times_group_caused_propagation[i], i));

    if (!props_group_ordered.empty()) {
        print_footer();
        print_simple_line(" No. propagations made by clause groups");
        print_header("group", "group name", "no. props");
        std::sort(props_group_ordered.rbegin(),props_group_ordered.rend());
        print_groups(props_group_ordered);
    }
}

void Logger::print_times_group_caused_conflict() const
{
    vector<pair<uint, uint> > confls_group_ordered;
    for (uint i = 0; i < times_group_caused_conflict.size(); i++)
        if (times_group_caused_conflict[i] > 0)
            confls_group_ordered.push_back(std::make_pair(times_group_caused_conflict[i], i));

    if (!confls_group_ordered.empty()) {
        print_footer();
        print_simple_line(" No. conflicts made by clause groups");
        print_header("group", "group name", "no. confl");
        std::sort(confls_group_ordered.rbegin(), confls_group_ordered.rend());
        print_groups(confls_group_ordered);
    }
}

template<class T>
void Logger::print_line(const uint& number, const string& name, const T& value) const
{
    cout << "|" << std::setw(FST_WIDTH) << number << "  " << std::setw(SND_WIDTH) << name << "  " << std::setw(TRD_WIDTH) << value << "|" << endl;
}

void Logger::print_header(const string& first, const string& second, const string& third) const
{
    cout << "|" << std::setw(FST_WIDTH) << first << "  " << std::setw(SND_WIDTH) << second << "  " << std::setw(TRD_WIDTH) << third << "|" << endl;
    print_footer();
}

void Logger::print_groups(const vector<pair<double, uint> >& to_print) const
{
    uint i = 0;
    typedef vector<pair<double, uint> >::const_iterator myiterator;
    for (myiterator it = to_print.begin(); it != to_print.end() && i < max_print_lines; it++, i++) {
        print_line(it->second+1, cut_name_to_size(groupnames[it->second]), it->first);
    }
    print_footer();
}

void Logger::print_groups(const vector<pair<uint, uint> >& to_print) const
{
    uint i = 0;
    typedef vector<pair<uint, uint> >::const_iterator myiterator;
    for (myiterator it = to_print.begin(); it != to_print.end() && i < max_print_lines; it++, i++) {
        print_line(it->second+1, cut_name_to_size(groupnames[it->second]), it->first);
    }
    print_footer();
}

void Logger::print_vars(const vector<pair<double, uint> >& to_print) const
{
    uint i = 0;
    for (vector<pair<double, uint> >::const_iterator it = to_print.begin(); it != to_print.end() && i < max_print_lines; it++, i++)
        print_line(it->second+1, cut_name_to_size(varnames[it->second]), it->first);
    
    print_footer();
}

void Logger::print_vars(const vector<pair<uint, uint> >& to_print) const
{
    uint i = 0;
    for (vector<pair<uint, uint> >::const_iterator it = to_print.begin(); it != to_print.end() && i < max_print_lines; it++, i++) {
        print_line(it->second+1, cut_name_to_size(varnames[it->second]), it->first);
    }
    
    print_footer();
}

template<class T>
void Logger::print_line(const string& str, const T& num) const
{
    cout << "|" << std::setw(FST_WIDTH+SND_WIDTH+4) << str << std::setw(TRD_WIDTH) << num << "|" << endl;
}

void Logger::print_simple_line(const string& str) const
{
    cout << "|" << std::setw(FST_WIDTH+SND_WIDTH+TRD_WIDTH+4) << str << "|" << endl;
}

void Logger::print_center_line(const string& str) const
{
    uint middle = (FST_WIDTH+SND_WIDTH+TRD_WIDTH+4-str.size())/2;
    int rest = FST_WIDTH+SND_WIDTH+TRD_WIDTH+4-middle*2-str.size();
    cout << "|" << std::setw(middle) << " " << str << std::setw(middle + rest) << " " << "|" << endl;
}

void Logger::print_branch_depth_distrib() const
{
    //cout << "--- Branch depth stats ---" << endl;

    const uint range = 20;
    map<uint, uint> range_stat;

    uint i = 0;
    for (vector<uint>::const_iterator it = branch_depth_distrib.begin(); it != branch_depth_distrib.end(); it++, i++) {
        range_stat[i/range] += *it;
    }

    print_footer();
    print_simple_line(" No. search branches with branch depth between");
    print_line("Branch depth between", "no. br.-s");
    print_footer();

    std::stringstream ss;
    ss << "branch_depths/branch_depth_file" << runid << "-" << S->starts << ".txt";
    ofstream branch_depth_file;
    branch_depth_file.open(ss.str().c_str());
    i = 0;
    
    for (map<uint, uint>::iterator it = range_stat.begin(); it != range_stat.end(); it++, i++) {
        std::stringstream ss2;
        ss2 << it->first*range << " - " << it->first*range + range-1;
        print_line(ss2.str(), it->second);

        if (branch_depth_file.is_open()) {
                branch_depth_file << i << "\t" << it->second << "\t";
            if (i %  5 == 0)
                branch_depth_file  << "\"" << it->first*range << "\"";
            else
                branch_depth_file << "\"\"";
            branch_depth_file << endl;
        }
    }
    if (branch_depth_file.is_open())
        branch_depth_file.close();
    print_footer();

}

void Logger::print_learnt_clause_distrib() const
{
    map<uint, uint> learnt_sizes;
    const vec<Clause*>& learnts = S->get_learnts();
    
    uint maximum = 0;
    
    for (uint i = 0; i < learnts.size(); i++)
    {
        uint size = learnts[i]->size();
        maximum = std::max(maximum, size);
        
        map<uint, uint>::iterator it = learnt_sizes.find(size);
        if (it == learnt_sizes.end())
            learnt_sizes[size] = 1;
        else
            it->second++;
    }
    
    learnt_sizes[0] = S->get_unitary_learnts_num();
    
    uint slice = (maximum+1)/max_print_lines + (bool)((maximum+1)%max_print_lines);
    
    print_footer();
    print_simple_line(" Learnt clause length distribution");
    print_line("Length between", "no. cl.");
    print_footer();
    
    uint until = slice;
    uint from = 0;
    while(until < maximum+1) {
        std::stringstream ss2;
        ss2 << from << " - " << until-1;
        
        uint sum = 0;
        for (; from < until; from++) {
            map<uint, uint>::const_iterator it = learnt_sizes.find(from);
            if (it != learnt_sizes.end())
                sum += it->second;
        }
        
        print_line(ss2.str(), sum);
        
        until += slice;
    }
    
    print_footer();
    
    print_leearnt_clause_graph_distrib(maximum, learnt_sizes);
}

void Logger::print_leearnt_clause_graph_distrib(const uint maximum, const map<uint, uint>& learnt_sizes) const
{
    uint no_slices = FST_WIDTH  + SND_WIDTH + TRD_WIDTH + 4-3;
    uint slice = (maximum+1)/no_slices + (bool)((maximum+1)%no_slices);
    uint until = slice;
    uint from = 0;
    vector<uint> slices;
    uint hmax = 0;
    while(until < maximum+1) {
        uint sum = 0;
        for (; from < until; from++) {
            map<uint, uint>::const_iterator it = learnt_sizes.find(from);
            if (it != learnt_sizes.end())
                sum += it->second;
        }
        slices.push_back(sum);
        until += slice;
        hmax = std::max(hmax, sum);
    }
    slices.resize(no_slices, 0);
    
    uint height = max_print_lines;
    uint hslice = (hmax+1)/height + (bool)((hmax+1)%height);
    if (hslice == 0) return;
    
    print_simple_line(" Learnt clause distribution in graph form");
    print_footer();
    string yaxis = "Number";
    uint middle = (height-yaxis.size())/2;
    
    for (int i = height-1; i > 0; i--) {
        cout << "| ";
        if (height-1-i >= middle && height-1-i-middle < yaxis.size())
            cout << yaxis[height-1-i-middle] << " ";
        else
            cout << "  ";
        for (uint i2 = 0; i2 != no_slices; i2++) {
            if (slices[i2]/hslice >= (uint)i) cout << "+";
            else cout << " ";
        }
        cout << "|" << endl;
    }
    print_center_line(" Learnt clause size");
    print_footer();
}

void Logger::print_general_stats() const
{
    print_footer();
    print_simple_line(" Standard MiniSat stats -- for all restarts until now");
    print_footer();
    print_line("Restart number", S->starts);
    print_line("Number of conflicts", S->conflicts);
    print_line("Number of decisions", S->decisions);
    print_line("Number of variables", S->order_heap.size());
    print_line("Number of clauses", S->nClauses());
    print_line("Number of literals in clauses",S->clauses_literals);
    print_line("Avg. literals per learnt clause",(double)S->learnts_literals/(double)S->nLearnts());
    print_line("Progress estimate (%):", S->progress_estimate*100.0);
    print_line("All unitary learnts until now", S->get_unitary_learnts_num());
    print_footer();
}

void Logger::print_learnt_unitaries(const uint from, const string display) const
{
    print_footer();
    print_simple_line(display);
    print_header("var", "name", "value");
    uint32_t until;
    if (S->decisionLevel() > 0)
        until = S->trail_lim[0];
    else
        until = S->trail.size();
    for (uint i = from; i < until; i++) {
        Var var = S->trail[i].var();
        bool value = !(S->trail[i].sign());
        print_line(var+1, cut_name_to_size(varnames[var]), value);
    }
    print_footer();
}


// Prints statistics on the console
void Logger::printstats() const
{
    assert(statistics_on);
    assert(varnames.size() == times_var_guessed.size());
    assert(varnames.size() == times_var_propagated.size());

    const uint fullwidth = FST_WIDTH+SND_WIDTH+TRD_WIDTH+4;
    cout << endl;
    cout << "+" << std::setfill('=') << std::setw(fullwidth) << "=" << "+" << endl;
    std::stringstream tmp;
    tmp << " STATS FOR RESTART NO. " << std::setw(3) << S->starts << "  BEGIN ";
    uint len = (fullwidth-2)/2-tmp.str().length()/2;
    uint len2 = len + tmp.str().length()%2 + (fullwidth-2)%2;
    cout << "||" << std::setfill('*') << std::setw(len) << "*" << tmp.str() << std::setw(len2) << "*" << "||" << endl;
    cout << "+" << std::setfill('=') << std::setw(fullwidth) << "=" << std::setfill(' ') << "+" << endl;
    
    cout.setf(std::ios_base::left);
    cout.precision(2);
    print_statistics_note();
    print_times_var_guessed();
    print_times_group_caused_propagation();
    print_times_group_caused_conflict();
    print_prop_order();
    print_confl_order();
    print_assign_var_order();
    print_branch_depth_distrib();
    print_learnt_clause_distrib();
    #ifdef USE_GAUSS
    print_matrix_stats();
    #endif //USE_GAUSS
    print_learnt_unitaries(0," Unitary clauses learnt until now");
    print_learnt_unitaries(last_unitary_learnt_clauses, " Unitary clauses during this restart");
    print_advanced_stats();
    print_general_stats();
}

#ifdef USE_GAUSS
void Logger::print_matrix_stats() const
{
    print_footer();
    print_simple_line(" Matrix statistics");
    print_footer();
    
    uint i = 0;
    for (vector<Gaussian*>::const_iterator it = S->gauss_matrixes.begin(), end = S->gauss_matrixes.end(); it != end; it++, i++) {
        std::stringstream s;
        s << "Matrix " << i << " enabled";
        std::stringstream tmp;
        tmp << std::boolalpha << !(*it)->get_disabled();
        print_line(s.str(), tmp.str());
        
        s.str("");
        s << "Matrix " << i << " called";
        print_line(s.str(), (*it)->get_called());
        
        s.str("");
        s << "Matrix " << i << " propagations";
        print_line(s.str(), (*it)->get_useful_prop());
        
        s.str("");
        s << "Matrix " << i << " conflicts";
        print_line(s.str(), (*it)->get_useful_confl());
    }
    
    print_footer();
}
#endif //USE_GAUSS

void Logger::print_advanced_stats() const
{
    print_footer();
    print_simple_line(" Advanced statistics - for only this restart");
    print_footer();
    print_line("Unitary learnts", S->get_unitary_learnts_num() - last_unitary_learnt_clauses);
    print_line("No. branches visited", no_conflicts);
    print_line("Avg. branch depth", (double)sum_conflict_depths/(double)no_conflicts);
    print_line("No. decisions", no_decisions);
    print_line("No. propagations",no_propagations);
    
    //printf("no progatations/no decisions (i.e. one decision gives how many propagations on average *for the whole search graph*): %f\n", (double)no_propagations/(double)no_decisions);
    //printf("no propagations/sum decisions on branches (if you look at one specific branch, what is the average number of propagations you will find?): %f\n", (double)no_propagations/(double)sum_decisions_on_branches);
    
    print_simple_line("sum decisions on branches/no. branches");
    print_simple_line(" (in a given branch, what is the avg.");
    print_line("  no. of decisions?)",(double)sum_decisions_on_branches/(double)no_conflicts);
    
    print_simple_line("sum propagations on branches/no. branches");
    print_simple_line(" (in a given branch, what is the");
    print_line("  avg. no. of propagations?)",(double)sum_propagations_on_branches/(double)no_conflicts);
    
    print_footer();
}

void Logger::print_statistics_note() const
{
    print_footer();
    print_simple_line("Statistics note: If you used CryptoMiniSat as");
    print_simple_line("a library then vars are all shifted by 1 here");
    print_simple_line("and in every printed output of the solver.");
    print_simple_line("This does not apply when you use CryptoMiniSat");
    print_simple_line("as a stand-alone program.");
    print_footer();
}

// resets all stored statistics. Might be useful, to generate statistics for each restart and not for the whole search in general
void Logger::reset_statistics()
{
    assert(S->decisionLevel() == 0);
    assert(times_var_guessed.size() == times_var_propagated.size());
    assert(times_group_caused_conflict.size() == times_group_caused_propagation.size());
    
    typedef vector<uint>::iterator vecit;
    for (vecit it = times_var_guessed.begin(); it != times_var_guessed.end(); it++)
        *it = 0;

    for (vecit it = times_var_propagated.begin(); it != times_var_propagated.end(); it++)
        *it = 0;

    for (vecit it = times_group_caused_conflict.begin(); it != times_group_caused_conflict.end(); it++)
        *it = 0;

    for (vecit it = times_group_caused_propagation.begin(); it != times_group_caused_propagation.end(); it++)
        *it = 0;

    for (vecit it = confls_by_group.begin(); it != confls_by_group.end(); it++)
        *it = 0;

    for (vecit it = props_by_group.begin(); it != props_by_group.end(); it++)
        *it = 0;

    typedef vector<MyAvg>::iterator avgIt;

    for (avgIt it = depths_of_propagations_for_group.begin(); it != depths_of_propagations_for_group.end(); it++) {
        it->sum = 0;
        it->num = 0;
    }

    for (avgIt it = depths_of_conflicts_for_group.begin(); it != depths_of_conflicts_for_group.end(); it++) {
        it->sum = 0;
        it->num = 0;
    }

    for (avgIt it = depths_of_assigns_for_var.begin(); it != depths_of_assigns_for_var.end(); it++) {
        it->sum = 0;
        it->num = 0;
    }
    for (uint i = 0; i < depths_of_assigns_unit.size(); i++)
        depths_of_assigns_unit[i] = false;
    
    for (uint i = 0; i < depths_of_propagations_unit.size(); i++)
        depths_of_propagations_unit[i] = false;

    sum_conflict_depths = 0;
    no_conflicts = 0;
    no_decisions = 0;
    no_propagations = 0;
    sum_decisions_on_branches = 0;
    sum_propagations_on_branches = 0;
    branch_depth_distrib.clear();
    last_unitary_learnt_clauses = S->get_unitary_learnts_num();
}

}; //NAMESPACE MINISAT
