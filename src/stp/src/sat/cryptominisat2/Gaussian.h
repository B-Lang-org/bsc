/***********************************************************************************
CryptoMiniSat -- Copyright (c) 2009 Mate Soos

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program.  If not, see <http://www.gnu.org/licenses/>.
**************************************************************************************************/

#ifndef GAUSSIAN_H
#define GAUSSIAN_H

#include <vector>
#include <limits>
#ifdef _MSC_VER
#include <msvc/stdint.h>
#else
#include <stdint.h>
#endif //_MSC_VER

#include "SolverTypes.h"
#include "Solver.h"
#include "GaussianConfig.h"
#include "PackedMatrix.h"
#include "BitArray.h"

//#define VERBOSE_DEBUG
//#define DEBUG_GAUSS

#ifdef VERBOSE_DEBUG
using std::vector;
using std::cout;
using std::endl;
#endif

namespace MINISAT
{
using namespace MINISAT;

class Clause;

class Gaussian
{
public:
    Gaussian(Solver& solver, const GaussianConfig& config, const uint matrix_no, const vector<XorClause*>& xorclauses);
    ~Gaussian();

    const bool full_init();
    llbool find_truths(vec<Lit>& learnt_clause, int& conflictC);

    //statistics
    void print_stats() const;
    void print_matrix_stats() const;
    const uint get_called() const;
    const uint get_useful_prop() const;
    const uint get_useful_confl() const;
    const bool get_disabled() const;
    const uint32_t get_unit_truths() const;
    void set_disabled(const bool toset);

    //functions used throughout the Solver
    void canceling(const uint sublevel);

protected:
    Solver& solver;
    
    //Gauss high-level configuration
    const GaussianConfig& config;
    const uint matrix_no;
    vector<XorClause*> xorclauses;

    enum gaussian_ret {conflict, unit_conflict, propagation, unit_propagation, nothing};
    gaussian_ret gaussian(Clause*& confl);

    vector<Var> col_to_var_original; //Matches columns to variables
    BitArray var_is_in; //variable is part of the the matrix. var_is_in's size is _minimal_ so you should check whether var_is_in.getSize() < var before issuing var_is_in[var]
    uint badlevel;

    class matrixset
    {
    public:
        PackedMatrix matrix; // The matrix, updated to reflect variable assignements
        BitArray var_is_set;
        vector<Var> col_to_var; // col_to_var[COL] tells which variable is at a given column in the matrix. Gives unassigned_var if the COL has been zeroed (i.e. the variable assigned)
        uint16_t num_rows; // number of active rows in the matrix. Unactive rows are rows that contain only zeros (and if they are conflicting, then the conflict has been treated)
        uint num_cols; // number of active columns in the matrix. The columns at the end that have all be zeroed are no longer active
        int least_column_changed; // when updating the matrix, this value contains the smallest column number that has been updated  (Gauss elim. can start from here instead of from column 0)
        vector<uint16_t> last_one_in_col; //last_one_in_col[COL] tells the last row+1 that has a '1' in that column. Used to reduce the burden of Gauss elim. (it only needs to look until that row)
        vector<uint16_t> first_one_in_row;
        uint removeable_cols; // the number of columns that have been zeroed out (i.e. assigned)
    };

    //Saved states
    vector<matrixset> matrix_sets; // The matrixsets for depths 'decision_from' + 0,  'decision_from' + only_nth_gaussian_save, 'decision_from' + 2*only_nth_gaussian_save, ... 'decision_from' + 'decision_until'.
    matrixset cur_matrixset; // The current matrixset, i.e. the one we are working on, or the last one we worked on

    //Varibales to keep Gauss state
    bool messed_matrix_vars_since_reversal;
    int gauss_last_level;
    vector<pair<Clause*, uint> > clauses_toclear;
    bool disabled; // Gauss is disabled
    
    //State of current elimnation
    vec<uint> propagatable_rows; //used to store which rows were deemed propagatable during elimination
    vector<unsigned char> changed_rows; //used to store which rows were deemed propagatable during elimination

    //Statistics
    uint useful_prop; //how many times Gauss gave propagation as a result
    uint useful_confl; //how many times Gauss gave conflict as a result
    uint called; //how many times called the Gauss
    uint32_t unit_truths; //how many unitary (i.e. decisionLevel 0) truths have been found

    //gauss init functions
    void init(); // Initalise gauss state
    void fill_matrix(matrixset& origMat); // Fills the origMat matrix
    uint select_columnorder(vector<uint16_t>& var_to_col, matrixset& origMat); // Fills var_to_col and col_to_var of the origMat matrix.

    //Main function
    uint eliminate(matrixset& matrix, uint& conflict_row); //does the actual gaussian elimination

    //matrix update functions
    void update_matrix_col(matrixset& matrix, const Var x, const uint col); // Update one matrix column
    void update_matrix_by_col_all(matrixset& m); // Update all columns, column-by-column (and not row-by-row)
    void set_matrixset_to_cur(); // Save the current matrixset, the cur_matrixset to matrix_sets
    //void update_matrix_by_row(matrixset& matrix) const;
    //void update_matrix_by_col(matrixset& matrix, const uint last_level) const;

    //conflict&propagation handling
    gaussian_ret handle_matrix_prop_and_confl(matrixset& m, uint row, Clause*& confl);
    void analyse_confl(const matrixset& m, const uint row, int32_t& maxlevel, uint& size, uint& best_row) const; // analyse conflcit to find the best conflict. Gets & returns the best one in 'maxlevel', 'size' and 'best row' (these are all UINT_MAX when calling this function first, i.e. when there is no other possible conflict to compare to the new in 'row')
    gaussian_ret handle_matrix_confl(Clause*& confl, const matrixset& m, const uint size, const uint maxlevel, const uint best_row);
    gaussian_ret handle_matrix_prop(matrixset& m, const uint row); // Handle matrix propagation at row 'row'
    vec<Lit> tmp_clause;

    //propagation&conflict handling
    void cancel_until_sublevel(const uint until_sublevel); // cancels until sublevel 'until_sublevel'. The var 'until_sublevel' must NOT go over the current level. I.e. this function is ONLY for moving inside the current level
    uint find_sublevel(const Var v) const; // find the sublevel (i.e. trail[X]) of a given variable

    //helper functions
    bool at_first_init() const;
    bool should_init() const;
    bool should_check_gauss(const uint decisionlevel, const uint starts) const;
    void disable_if_necessary();
    void reset_stats();
    void update_last_one_in_col(matrixset& m);
    
private:
    
    //debug functions
    bool check_no_conflict(matrixset& m) const; // Are there any conflicts that the matrixset 'm' causes?
    const bool nothing_to_propagate(matrixset& m) const; // Are there any conflicts of propagations that matrixset 'm' clauses?
    template<class T>
    void print_matrix_row(const T& row) const; // Print matrix row 'row'
    template<class T>
    void print_matrix_row_with_assigns(const T& row) const;
    void check_matrix_against_varset(PackedMatrix& matrix,const matrixset& m) const;
    const bool check_last_one_in_cols(matrixset& m) const;
    const void check_first_one_in_row(matrixset& m, const uint j);
    void print_matrix(matrixset& m) const;
    void print_last_one_in_cols(matrixset& m) const;
    static const string lbool_to_string(const lbool toprint);
};

inline bool Gaussian::should_init() const
{
    return (config.decision_until > 0);
}

inline bool Gaussian::should_check_gauss(const uint decisionlevel, const uint starts) const
{
    return (!disabled
            && decisionlevel < config.decision_until);
}

inline void Gaussian::canceling(const uint sublevel)
{
    if (disabled)
        return;
    uint a = 0;
    for (int i = clauses_toclear.size()-1; i >= 0 && clauses_toclear[i].second > sublevel; i--) {
        solver.clauseAllocator.clauseFree(clauses_toclear[i].first);
        a++;
    }
    clauses_toclear.resize(clauses_toclear.size()-a);
    
    if (messed_matrix_vars_since_reversal)
        return;
    int c = std::min((int)gauss_last_level, (int)(solver.trail.size())-1);
    for (; c >= (int)sublevel; c--) {
        Var var  = solver.trail[c].var();
        if (var < var_is_in.getSize()
            && var_is_in[var]
            && cur_matrixset.var_is_set[var]) {
        messed_matrix_vars_since_reversal = true;
        return;
        }
    }
}

inline const uint32_t Gaussian::get_unit_truths() const
{
    return unit_truths;
}

inline const uint Gaussian::get_called() const
{
    return called;
}

inline const uint Gaussian::get_useful_prop() const
{
    return useful_prop;
}

inline const uint Gaussian::get_useful_confl() const
{
    return useful_confl;
}

inline const bool Gaussian::get_disabled() const
{
    return disabled;
}

inline void Gaussian::set_disabled(const bool toset)
{
    disabled = toset;
}

std::ostream& operator << (std::ostream& os, const vec<Lit>& v);

}; //NAMESPACE MINISAT

#endif //GAUSSIAN_H
