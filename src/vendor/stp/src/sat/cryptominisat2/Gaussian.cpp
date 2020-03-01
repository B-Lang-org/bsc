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

#include "Gaussian.h"

#include <iostream>
#include <iomanip>
#include "Clause.h"
#include <algorithm>
#include "ClauseCleaner.h"

using std::ostream;
using std::cout;
using std::endl;

#ifdef VERBOSE_DEBUG
#include <iterator>
#endif

namespace MINISAT
{
using namespace MINISAT;
static const uint16_t unassigned_col = std::numeric_limits<uint16_t>::max();
static const Var unassigned_var = std::numeric_limits<Var>::max();

ostream& operator << (ostream& os, const vec<Lit>& v)
{
    for (uint32_t i = 0; i != v.size(); i++) {
        if (v[i].sign()) os << "-";
        os << v[i].var()+1 << " ";
    }

    return os;
}

Gaussian::Gaussian(Solver& _solver, const GaussianConfig& _config, const uint _matrix_no, const vector<XorClause*>& _xorclauses) :
        solver(_solver)
        , config(_config)
        , matrix_no(_matrix_no)
        , xorclauses(_xorclauses)
        , messed_matrix_vars_since_reversal(true)
        , gauss_last_level(0)
        , disabled(false)
        , useful_prop(0)
        , useful_confl(0)
        , called(0)
        , unit_truths(0)
{
}

Gaussian::~Gaussian()
{
    for (uint i = 0; i < clauses_toclear.size(); i++)
        solver.clauseAllocator.clauseFree(clauses_toclear[i].first);
}

inline void Gaussian::set_matrixset_to_cur()
{
    uint level = solver.decisionLevel() / config.only_nth_gauss_save;
    assert(level <= matrix_sets.size());
    
    if (level == matrix_sets.size())
        matrix_sets.push_back(cur_matrixset);
    else
        matrix_sets[level] = cur_matrixset;
}

const bool Gaussian::full_init()
{
    assert(solver.ok);
    
    if (!should_init()) return true;
    reset_stats();
    uint32_t last_trail_size = solver.trail.size();
    
    bool do_again_gauss = true;
    while (do_again_gauss) {
        do_again_gauss = false;
        solver.clauseCleaner->cleanClauses(solver.xorclauses, ClauseCleaner::xorclauses);
        if (!solver.ok) return false;
        init();
        Clause* confl;
        gaussian_ret g = gaussian(confl);
        switch (g) {
        case unit_conflict:
        case conflict:
            solver.ok = false;
            return false;
        case unit_propagation:
        case propagation:
            unit_truths += last_trail_size - solver.trail.size();
            do_again_gauss = true;
            solver.ok = (solver.propagate().isNULL());
            if (!solver.ok) return false;
            break;
        case nothing:
            break;
        }
    }

    return true;
}

void Gaussian::init()
{
    assert(solver.decisionLevel() == 0);

    fill_matrix(cur_matrixset);
    if (!cur_matrixset.num_rows || !cur_matrixset.num_cols) {
        disabled = true;
        badlevel = 0;
        return;
    }
    
    matrix_sets.clear();
    matrix_sets.push_back(cur_matrixset);
    gauss_last_level = solver.trail.size();
    messed_matrix_vars_since_reversal = false;
    badlevel = UINT_MAX;

    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Gaussian init finished." << endl;
    #endif
}

uint Gaussian::select_columnorder(vector<uint16_t>& var_to_col, matrixset& origMat)
{
    var_to_col.resize(solver.nVars(), unassigned_col);

    uint num_xorclauses  = 0;
    for (uint32_t i = 0; i != xorclauses.size(); i++) {
        XorClause& c = *xorclauses[i];
        if (c.removed()) continue;
        num_xorclauses++;
        
        for (uint i2 = 0; i2 < c.size(); i2++) {
            assert(solver.assigns[c[i2].var()].isUndef());
            var_to_col[c[i2].var()] = unassigned_col - 1;
        }
    }
    
    uint largest_used_var = 0;
    for (uint i = 0; i < var_to_col.size(); i++)
        if (var_to_col[i] != unassigned_col)
            largest_used_var = i;
    var_to_col.resize(largest_used_var + 1);
    
    var_is_in.resize(var_to_col.size(), 0);
    origMat.var_is_set.resize(var_to_col.size(), 0);

    origMat.col_to_var.clear();
    vector<Var> vars(solver.nVars());
    if (!config.orderCols) {
        for (uint32_t i = 0; i < solver.nVars(); i++) {
            vars.push_back(i);
        }
        std::random_shuffle(vars.begin(), vars.end());
    }

    Heap<Solver::VarOrderLt> order_heap(solver.order_heap);
    uint32_t iterReduceIt = 0;
    while ((config.orderCols && !order_heap.empty()) || (!config.orderCols && iterReduceIt < vars.size()))
    {
        Var v;
        if (config.orderCols) v = order_heap.removeMin();
        else v = vars[iterReduceIt++];
        if (var_to_col[v] == 1) {
            #ifdef DEBUG_GAUSS
            vector<uint>::iterator it =
                std::find(origMat.col_to_var.begin(), origMat.col_to_var.end(), v);
            assert(it == origMat.col_to_var.end());
            #endif
            
            origMat.col_to_var.push_back(v);
            var_to_col[v] = origMat.col_to_var.size()-1;
            var_is_in.setBit(v);
        }
    }

    //for the ones that were not in the order_heap, but are marked in var_to_col
    for (uint v = 0; v != var_to_col.size(); v++) {
        if (var_to_col[v] == unassigned_col - 1) {
            origMat.col_to_var.push_back(v);
            var_to_col[v] = origMat.col_to_var.size() -1;
            var_is_in.setBit(v);
        }
    }

    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")col_to_var:";
    std::copy(origMat.col_to_var.begin(), origMat.col_to_var.end(), std::ostream_iterator<uint>(cout, ","));
    cout << endl;
    #endif

    return num_xorclauses;
}

void Gaussian::fill_matrix(matrixset& origMat)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Filling matrix" << endl;
    #endif

    vector<uint16_t> var_to_col;
    origMat.num_rows = select_columnorder(var_to_col, origMat);
    origMat.num_cols = origMat.col_to_var.size();
    col_to_var_original = origMat.col_to_var;
    changed_rows.resize(origMat.num_rows);
    memset(&changed_rows[0], 0, sizeof(char)*changed_rows.size());

    origMat.last_one_in_col.resize(origMat.num_cols);
    std::fill(origMat.last_one_in_col.begin(), origMat.last_one_in_col.end(), origMat.num_rows);
    origMat.first_one_in_row.resize(origMat.num_rows);
    
    origMat.removeable_cols = 0;
    origMat.least_column_changed = -1;
    origMat.matrix.resize(origMat.num_rows, origMat.num_cols);

    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")matrix size:" << origMat.num_rows << "," << origMat.num_cols << endl;
    #endif

    uint matrix_row = 0;
    for (uint32_t i = 0; i != xorclauses.size(); i++) {
        const XorClause& c = *xorclauses[i];
        if (c.removed()) continue;

        origMat.matrix.getVarsetAt(matrix_row).set(c, var_to_col, origMat.num_cols);
        origMat.matrix.getMatrixAt(matrix_row).set(c, var_to_col, origMat.num_cols);
        matrix_row++;
    }
    assert(origMat.num_rows == matrix_row);
}

void Gaussian::update_matrix_col(matrixset& m, const Var var, const uint col)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Updating matrix var " << var+1 << " (col " << col << ", m.last_one_in_col[col]: " << m.last_one_in_col[col] << ")" << endl;
    cout << "m.num_rows:" << m.num_rows << endl;
    #endif
    
    #ifdef DEBUG_GAUSS
    assert(col < m.num_cols);
    #endif
    
    m.least_column_changed = std::min(m.least_column_changed, (int)col);
    PackedMatrix::iterator this_row = m.matrix.beginMatrix();
    uint row_num = 0;

    if (solver.assigns[var].getBool()) {
        for (uint end = m.last_one_in_col[col];  row_num != end; ++this_row, row_num++) {
            if ((*this_row)[col]) {
                changed_rows[row_num] = true;
                (*this_row).invert_is_true();
                (*this_row).clearBit(col);
            }
        }
    } else {
        for (uint end = m.last_one_in_col[col];  row_num != end; ++this_row, row_num++) {
            if ((*this_row)[col]) {
                changed_rows[row_num] = true;
                (*this_row).clearBit(col);
            }
        }
    }

    #ifdef DEBUG_GAUSS
    bool c = false;
    for(PackedMatrix::iterator r = m.matrix.beginMatrix(), end = r + m.matrix.getSize(); r != end; ++r)
        c |= (*r)[col];
    assert(!c);
    #endif

    m.removeable_cols++;
    m.col_to_var[col] = unassigned_var;
    m.var_is_set.setBit(var);
}

void Gaussian::update_matrix_by_col_all(matrixset& m)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Updating matrix." << endl;
    print_matrix(m);
    uint num_updated = 0;
    #endif
    
    #ifdef DEBUG_GAUSS
    assert(nothing_to_propagate(cur_matrixset));
    assert(solver.decisionLevel() == 0 || check_last_one_in_cols(m));
    #endif
    
    memset(&changed_rows[0], 0, sizeof(char)*changed_rows.size());

    uint last = 0;
    uint col = 0;
    for (const Var *it = &m.col_to_var[0], *end = it + m.num_cols; it != end; col++, it++) {
        if (*it != unassigned_var && solver.assigns[*it].isDef()) {
            update_matrix_col(m, *it, col);
            last++;
            #ifdef VERBOSE_DEBUG
            num_updated++;
            #endif
        } else
            last = 0;
    }
    m.num_cols -= last;
    
    #ifdef DEBUG_GAUSS
    check_matrix_against_varset(m.matrix, m);
    #endif

    #ifdef VERBOSE_DEBUG
    cout << "Matrix update finished, updated " << num_updated << " cols" << endl;
    print_matrix(m);
    #endif
    
    /*cout << "num_rows:" << m.num_rows;
    cout << " num_rows diff:" << origMat.num_rows - m.num_rows << endl;
    cout << "num_cols:" << col_to_var_original.size();
    cout << " num_cols diff:" << col_to_var_original.size() - m.col_to_var.size() << endl;
    cout << "removeable cols:" << m.removeable_cols << endl;*/
}

inline void Gaussian::update_last_one_in_col(matrixset& m)
{
    for (uint16_t* i = &m.last_one_in_col[0]+m.last_one_in_col.size()-1, *end = &m.last_one_in_col[0]-1; i != end && *i >= m.num_rows; i--)
        *i = m.num_rows;
}

Gaussian::gaussian_ret Gaussian::gaussian(Clause*& confl)
{
    if (solver.decisionLevel() >= badlevel)
        return nothing;

    if (messed_matrix_vars_since_reversal) {
        #ifdef VERBOSE_DEBUG
        cout << "(" << matrix_no << ")matrix needs copy before update" << endl;
        #endif
        
        const uint level = solver.decisionLevel() / config.only_nth_gauss_save;
        assert(level < matrix_sets.size());
        cur_matrixset = matrix_sets[level];
    }
    update_last_one_in_col(cur_matrixset);
    update_matrix_by_col_all(cur_matrixset);

    messed_matrix_vars_since_reversal = false;
    gauss_last_level = solver.trail.size();
    badlevel = UINT_MAX;

    propagatable_rows.clear();
    uint conflict_row = UINT_MAX;
    uint last_row = eliminate(cur_matrixset, conflict_row);
    #ifdef DEBUG_GAUSS
    check_matrix_against_varset(cur_matrixset.matrix, cur_matrixset);
    #endif
    
    gaussian_ret ret;
    //There is no early abort, so this is unneeded
    /*if (conflict_row != UINT_MAX) {
        uint maxlevel = UINT_MAX;
        uint size = UINT_MAX;
        uint best_row = UINT_MAX;
        analyse_confl(cur_matrixset, conflict_row, maxlevel, size, best_row);
        ret = handle_matrix_confl(confl, cur_matrixset, size, maxlevel, best_row);
    } else {*/
        ret = handle_matrix_prop_and_confl(cur_matrixset, last_row, confl);
    //}
    #ifdef DEBUG_GAUSS
    assert(ret == conflict || nothing_to_propagate(cur_matrixset));
    #endif
    
    if (!cur_matrixset.num_cols || !cur_matrixset.num_rows) {
        badlevel = solver.decisionLevel();
        return nothing;
    }
    
    if (ret == nothing &&
        solver.decisionLevel() % config.only_nth_gauss_save == 0)
        set_matrixset_to_cur();

    #ifdef VERBOSE_DEBUG
    if (ret == nothing)
        cout << "(" << matrix_no << ")Useless. ";
    else
        cout << "(" << matrix_no << ")Useful. ";
    cout << "(" << matrix_no << ")Useful prop in " << ((double)useful_prop/(double)called)*100.0 << "%" << endl;
    cout << "(" << matrix_no << ")Useful confl in " << ((double)useful_confl/(double)called)*100.0 << "%" << endl;
    #endif

    return ret;
}

uint Gaussian::eliminate(matrixset& m, uint& conflict_row)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")";
    cout << "Starting elimination" << endl;
    cout << "m.least_column_changed:" << m.least_column_changed << endl;
    print_last_one_in_cols(m);
    
    uint number_of_row_additions = 0;
    uint no_exchanged = 0;
    #endif
    
    if (m.least_column_changed == INT_MAX) {
        #ifdef VERBOSE_DEBUG
        cout << "Nothing to eliminate" << endl;
        #endif
        
        return m.num_rows;
    }
    
    
    #ifdef DEBUG_GAUSS
    assert(solver.decisionLevel() == 0 || check_last_one_in_cols(m));
    #endif

    uint i = 0;
    uint j = (config.iterativeReduce) ? m.least_column_changed + 1 : 0;
    PackedMatrix::iterator beginIt = m.matrix.beginMatrix();
    PackedMatrix::iterator rowIt = m.matrix.beginMatrix();

    #ifdef DEBUG_GAUSS
    check_first_one_in_row(m, j);
    #endif
    
    if (j) {
        uint16_t until = std::min(m.last_one_in_col[m.least_column_changed] - 1, (int)m.num_rows);
        if (j-1 > m.first_one_in_row[m.num_rows-1])
            until = m.num_rows;
        for (;i != until; i++, ++rowIt) if (changed_rows[i] && (*rowIt).popcnt_is_one(m.first_one_in_row[i]))
            propagatable_rows.push(i);
    }
    
    #ifdef VERBOSE_DEBUG
    cout << "At while() start: i,j = " << i << ", " << j << endl;
    cout << "num_rows:" << m.num_rows << " num_cols:" << m.num_cols << endl;
    #endif
    
    if (j > m.num_cols) {
        #ifdef VERBOSE_DEBUG
        cout << "Going straight to finish" << endl;
        #endif
        goto finish;
    }
    
    #ifdef DEBUG_GAUSS
    assert(i <= m.num_rows && j <= m.num_cols);
    #endif

    while (i != m.num_rows && j != m.num_cols) {
        //Find pivot in column j, starting in row i:

        if (m.col_to_var[j] == unassigned_var) {
            j++;
            continue;
        }

        PackedMatrix::iterator this_matrix_row = rowIt;
        PackedMatrix::iterator end = beginIt + m.last_one_in_col[j];
        for (; this_matrix_row != end; ++this_matrix_row) {
            if ((*this_matrix_row)[j])
                break;
        }

        if (this_matrix_row != end) {

            //swap rows i and maxi, but do not change the value of i;
            if (this_matrix_row != rowIt) {
                #ifdef VERBOSE_DEBUG
                no_exchanged++;
                #endif
                
                //Would early abort, but would not find the best conflict (and would be expensive)
                //if (matrix_row_i.is_true() && matrix_row_i.isZero()) {
                //    conflict_row = i;
                //    return 0;
                //}
                (*rowIt).swapBoth(*this_matrix_row);
            }
            #ifdef DEBUG_GAUSS
            assert(m.matrix.getMatrixAt(i).popcnt(j) == m.matrix.getMatrixAt(i).popcnt());
            assert(m.matrix.getMatrixAt(i)[j]);
            #endif

            if ((*rowIt).popcnt_is_one(j))
                propagatable_rows.push(i);

            //Now A[i,j] will contain the old value of A[maxi,j];
            ++this_matrix_row;
            for (; this_matrix_row != end; ++this_matrix_row) if ((*this_matrix_row)[j]) {
                //subtract row i from row u;
                //Now A[u,j] will be 0, since A[u,j] - A[i,j] = A[u,j] -1 = 0.
                #ifdef VERBOSE_DEBUG
                number_of_row_additions++;
                #endif
                
                (*this_matrix_row).xorBoth(*rowIt);
                //Would early abort, but would not find the best conflict (and would be expensive)
                //if (it->is_true() &&it->isZero()) {
                //    conflict_row = i2;
                //    return 0;
                //}
            }
            m.first_one_in_row[i] = j;
            i++;
            ++rowIt;
            m.last_one_in_col[j] = i;
        } else {
            m.first_one_in_row[i] = j;
            m.last_one_in_col[j] = i + 1;
        }
        j++;
    }
    
    finish:

    m.least_column_changed = INT_MAX;

    #ifdef VERBOSE_DEBUG
    cout << "Finished elimination" << endl;
    cout << "Returning with i,j:" << i << ", " << j << "(" << m.num_rows << ", " << m.num_cols << ")" << endl;
    print_matrix(m);
    print_last_one_in_cols(m);
    cout << "(" << matrix_no << ")Exchanged:" << no_exchanged << " row additions:" << number_of_row_additions << endl;
    #endif
    
    #ifdef DEBUG_GAUSS
    assert(check_last_one_in_cols(m));
    uint row = 0;
    uint col = 0;
    for (; col < m.num_cols && row < m.num_rows && row < i ; col++) {
        assert(m.matrix.getMatrixAt(row).popcnt() == m.matrix.getMatrixAt(row).popcnt(col));
        assert(!(m.col_to_var[col] == unassigned_var && m.matrix.getMatrixAt(row)[col]));
        if (m.col_to_var[col] == unassigned_var || !m.matrix.getMatrixAt(row)[col]) {
            #ifdef VERBOSE_DEBUG
            cout << "row:" << row << " col:" << col << " m.last_one_in_col[col]-1: " << m.last_one_in_col[col]-1 << endl;
            #endif
            assert(m.col_to_var[col] == unassigned_var || std::min((uint16_t)(m.last_one_in_col[col]-1), m.num_rows) == row);
            continue;
        }
        row++;
    }
    #endif

    return i;
}

Gaussian::gaussian_ret Gaussian::handle_matrix_confl(Clause*& confl, const matrixset& m, const uint size, const uint maxlevel, const uint best_row)
{
    assert(best_row != UINT_MAX);

    m.matrix.getVarsetAt(best_row).fill(tmp_clause, solver.assigns, col_to_var_original);
    confl = (Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, false, solver.learnt_clause_group++);
    Clause& cla = *confl;
    #ifdef STATS_NEEDED
    if (solver.dynamic_behaviour_analysis)
        solver.logger.set_group_name(confl->getGroup(), "learnt gauss clause");
    #endif
    
    if (cla.size() <= 1) {
        solver.ok = false;
        return unit_conflict;
    }

    assert(cla.size() >= 2);
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Found conflict:";
    cla.plainPrint();
    #endif

    if (maxlevel != solver.decisionLevel()) {
        #ifdef STATS_NEEDED
        if (solver.dynamic_behaviour_analysis)
            solver.logger.conflict(Logger::gauss_confl_type, maxlevel, confl->getGroup(), *confl);
        #endif
        solver.cancelUntil(maxlevel);
    }
    const uint curr_dec_level = solver.decisionLevel();
    assert(maxlevel == curr_dec_level);
    
    uint maxsublevel = 0;
    uint maxsublevel_at = UINT_MAX;
    for (uint i = 0, size = cla.size(); i != size; i++) if (solver.level[cla[i].var()] == (int32_t)curr_dec_level) {
        uint tmp = find_sublevel(cla[i].var());
        if (tmp >= maxsublevel) {
            maxsublevel = tmp;
            maxsublevel_at = i;
        }
    }
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ") || Sublevel of confl: " << maxsublevel << " (due to var:" << cla[maxsublevel_at].var()-1 << ")" << endl;
    #endif
    
    Lit tmp(cla[maxsublevel_at]);
    cla[maxsublevel_at] = cla[1];
    cla[1] = tmp;

    cancel_until_sublevel(maxsublevel+1);
    messed_matrix_vars_since_reversal = true;
    return conflict;
}

Gaussian::gaussian_ret Gaussian::handle_matrix_prop_and_confl(matrixset& m, uint last_row, Clause*& confl)
{
    int32_t maxlevel = std::numeric_limits<int32_t>::max();
    uint size = UINT_MAX;
    uint best_row = UINT_MAX;

    for (uint row = last_row; row != m.num_rows; row++) {
        #ifdef DEBUG_GAUSS
        assert(m.matrix.getMatrixAt(row).isZero());
        #endif
        if (m.matrix.getMatrixAt(row).is_true())
            analyse_confl(m, row, maxlevel, size, best_row);
    }

    if (maxlevel != std::numeric_limits<int32_t>::max())
        return handle_matrix_confl(confl, m, size, maxlevel, best_row);

    #ifdef DEBUG_GAUSS
    assert(check_no_conflict(m));
    assert(last_row == 0 || !m.matrix.getMatrixAt(last_row-1).isZero());
    #endif
    
    #ifdef VERBOSE_DEBUG
    cout << "Resizing matrix to num_rows = " << last_row << endl;
    #endif
    m.num_rows = last_row;
    m.matrix.resizeNumRows(m.num_rows);

    gaussian_ret ret = nothing;

    uint num_props = 0;
    for (const uint* prop_row = propagatable_rows.getData(), *end = prop_row + propagatable_rows.size(); prop_row != end; prop_row++ ) {
        //this is a "000..1..0000000X" row. I.e. it indicates a propagation
        ret = handle_matrix_prop(m, *prop_row);
        num_props++;
        if (ret == unit_propagation) {
            #ifdef VERBOSE_DEBUG
            cout << "(" << matrix_no << ")Unit prop! Breaking from prop examination" << endl;
            #endif
            return  unit_propagation;
        }
    }
    #ifdef VERBOSE_DEBUG
    if (num_props > 0) cout << "(" << matrix_no << ")Number of props during gauss:" << num_props << endl;
    #endif

    return ret;
}

uint Gaussian::find_sublevel(const Var v) const
{
    for (int i = solver.trail.size()-1; i >= 0; i --)
        if (solver.trail[i].var() == v) return i;
    
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Oooops! Var " << v+1 << " does not have a sublevel!! (so it must be undefined)" << endl;
    #endif
    
    assert(false);
    return 0;
}

void Gaussian::cancel_until_sublevel(const uint until_sublevel)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Canceling until sublevel " << until_sublevel << endl;
    #endif
    
    for (vector<Gaussian*>::iterator gauss = solver.gauss_matrixes.begin(), end= solver.gauss_matrixes.end(); gauss != end; gauss++)
        if (*gauss != this) (*gauss)->canceling(until_sublevel);

        for (int sublevel = solver.trail.size()-1; sublevel >= (int)until_sublevel; sublevel--) {
        Var var  = solver.trail[sublevel].var();
        #ifdef VERBOSE_DEBUG
        cout << "(" << matrix_no << ")Canceling var " << var+1 << endl;
        #endif

        #ifdef USE_OLD_POLARITIES
        solver.polarity[var] = solver.oldPolarity[var];
        #endif //USE_OLD_POLARITIES
        solver.assigns[var] = l_Undef;
        solver.insertVarOrder(var);
    }
    solver.trail.shrink(solver.trail.size() - until_sublevel);
    
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")Canceling sublevel finished." << endl;
    #endif
}

void Gaussian::analyse_confl(const matrixset& m, const uint row, int32_t& maxlevel, uint& size, uint& best_row) const
{
    assert(row < m.num_rows);

    //this is a "000...00000001" row. I.e. it indicates we are on the wrong branch
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")matrix conflict found!" << endl;
    cout << "(" << matrix_no << ")conflict clause's vars: ";
    print_matrix_row_with_assigns(m.matrix.getVarsetAt(row));
    cout << endl;
    
    cout << "(" << matrix_no << ")corresponding matrix's row (should be empty): ";
    print_matrix_row(m.matrix.getMatrixAt(row));
    cout << endl;
    #endif

    int32_t this_maxlevel = 0;
    unsigned long int var = 0;
    uint this_size = 0;
    while (true) {
        var = m.matrix.getVarsetAt(row).scan(var);
        if (var == ULONG_MAX) break;

        const Var real_var = col_to_var_original[var];
        assert(real_var < solver.nVars());

        if (solver.level[real_var] > this_maxlevel)
            this_maxlevel = solver.level[real_var];
        var++;
        this_size++;
    }

    //the maximum of all lit's level must be lower than the max. level of the current best clause (or this clause must be either empty or unit clause)
    if (!(
                (this_maxlevel < maxlevel)
                || (this_maxlevel == maxlevel && this_size < size)
                || (this_size <= 1)
            )) {
        assert(maxlevel != std::numeric_limits<int32_t>::max());
    
        #ifdef VERBOSE_DEBUG
        cout << "(" << matrix_no << ")Other found conflict just as good or better.";
        cout << "(" << matrix_no << ") || Old maxlevel:" << maxlevel << " new maxlevel:" << this_maxlevel;
        cout << "(" << matrix_no << ") || Old size:" << size << " new size:" << this_size << endl;
        //assert(!(maxlevel != UINT_MAX && maxlevel != this_maxlevel)); //NOTE: only holds if gauss is executed at each level
        #endif
        
        return;
    }


    #ifdef VERBOSE_DEBUG
    if (maxlevel != std::numeric_limits<int32_t>::max())
        cout << "(" << matrix_no << ")Better conflict found.";
    else
        cout << "(" << matrix_no << ")Found a possible conflict.";

    cout << "(" << matrix_no << ") || Old maxlevel:" << maxlevel << " new maxlevel:" << this_maxlevel;
    cout << "(" << matrix_no << ") || Old size:" << size << " new size:" << this_size << endl;
    #endif

    maxlevel = this_maxlevel;
    size = this_size;
    best_row = row;
}

Gaussian::gaussian_ret Gaussian::handle_matrix_prop(matrixset& m, const uint row)
{
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")matrix prop found!" << endl;
    cout << m.matrix.getMatrixAt(row) << endl;
    cout << "(" << matrix_no << ")matrix row:";
    print_matrix_row(m.matrix.getMatrixAt(row));
    cout << endl;
    #endif

    m.matrix.getVarsetAt(row).fill(tmp_clause, solver.assigns, col_to_var_original);
    Clause& cla = *(Clause*)solver.clauseAllocator.XorClause_new(tmp_clause, false, solver.learnt_clause_group++);
    #ifdef VERBOSE_DEBUG
    cout << "(" << matrix_no << ")matrix prop clause: ";
    cla.plainPrint();
    cout << endl;
    #endif
    
    assert(m.matrix.getMatrixAt(row).is_true() == !cla[0].sign());
    assert(solver.assigns[cla[0].var()].isUndef());
    if (cla.size() == 1) {
        solver.cancelUntil(0);
        solver.uncheckedEnqueue(cla[0]);
        solver.clauseAllocator.clauseFree(&cla);
        return unit_propagation;
    }

    clauses_toclear.push_back(std::make_pair(&cla, solver.trail.size()-1));
    #ifdef STATS_NEEDED
    if (solver.dynamic_behaviour_analysis)
        solver.logger.set_group_name(cla.getGroup(), "gauss prop clause");
    #endif
    solver.uncheckedEnqueue(cla[0], &cla);

    return propagation;
}

void Gaussian::disable_if_necessary()
{
    if (//nof_conflicts >= 0
        //&& conflictC >= nof_conflicts/8
        !config.dontDisable
        && called > 50
        && useful_confl*2+useful_prop < (uint)((double)called*0.05) )
            disabled = true;
}

llbool Gaussian::find_truths(vec<Lit>& learnt_clause, int& conflictC)
{
    Clause* confl;

    disable_if_necessary();
    if (should_check_gauss(solver.decisionLevel(), solver.starts)) {
        called++;
        gaussian_ret g = gaussian(confl);
        
        switch (g) {
        case conflict: {
            useful_confl++;
            llbool ret = solver.handle_conflict(learnt_clause, confl, conflictC, true);
            solver.clauseAllocator.clauseFree(confl);
            
            if (ret != l_Nothing) return ret;
            return l_Continue;
        }
        case unit_propagation:
            unit_truths++;
        case propagation:
            useful_prop++;
            return l_Continue;
        case unit_conflict: {
            unit_truths++;
            useful_confl++;
            if (confl->size() == 0) {
                solver.clauseAllocator.clauseFree(confl);
                return l_False;
            }

            Lit lit = (*confl)[0];
            #ifdef STATS_NEEDED
            if (solver.dynamic_behaviour_analysis)
                solver.logger.conflict(Logger::gauss_confl_type, 0, confl->getGroup(), *confl);
            #endif
            
            solver.cancelUntil(0);
            
            if (solver.assigns[lit.var()].isDef()) {
                solver.clauseAllocator.clauseFree(confl);
                return l_False;
            }
            
            solver.uncheckedEnqueue(lit);
            
            solver.clauseAllocator.clauseFree(confl);
            return l_Continue;
        }
        case nothing:
            break;
        }
    }

    return l_Nothing;
}

template<class T>
void Gaussian::print_matrix_row(const T& row) const
{
    unsigned long int var = 0;
    while (true) {
        var = row.scan(var);
        if (var == ULONG_MAX) break;

        else cout << col_to_var_original[var]+1 << ", ";
        var++;
    }
    cout << "final:" << row.is_true() << endl;;
}

template<class T>
void Gaussian::print_matrix_row_with_assigns(const T& row) const
{
    unsigned long int col = 0;
    while (true) {
        col = row.scan(col);
        if (col == ULONG_MAX) break;
        
        else {
            Var var = col_to_var_original[col];
            cout << var+1 << "(" << lbool_to_string(solver.assigns[var]) << ")";
            cout << ", ";
        }
        col++;
    }
    if (!row.is_true()) cout << "xor_clause_inverted";
}

const string Gaussian::lbool_to_string(const lbool toprint)
{
    if (toprint == l_True)
            return "true";
    if (toprint == l_False)
            return "false";
    if (toprint == l_Undef)
            return "undef";
    
    assert(false);
    return "";
}


void Gaussian::print_stats() const
{
    if (called > 0) {
        cout.setf(std::ios::fixed);
        std::cout << " Gauss(" << matrix_no << ") useful";
        cout << " prop: " << std::setprecision(2) << std::setw(5) << ((double)useful_prop/(double)called)*100.0 << "% ";
        cout << " confl: " << std::setprecision(2) << std::setw(5) << ((double)useful_confl/(double)called)*100.0 << "% ";
        if (disabled) std::cout << "disabled";
    } else
        std::cout << " Gauss(" << matrix_no << ") not called.";
}

void Gaussian::print_matrix_stats() const
{
    cout << "matrix size: " << cur_matrixset.num_rows << "  x " << cur_matrixset.num_cols << endl;
}


void Gaussian::reset_stats()
{
    useful_prop = 0;
    useful_confl = 0;
    called = 0;
    disabled = false;
}

bool Gaussian::check_no_conflict(matrixset& m) const
{
    uint row = 0;
    for(PackedMatrix::iterator r = m.matrix.beginMatrix(), end = m.matrix.endMatrix(); r != end; ++r, ++row) {
        if ((*r).is_true() && (*r).isZero()) {
            cout << "Conflict at row " << row << endl;
            return false;
        }
    }
    return true;
}

void Gaussian::print_matrix(matrixset& m) const
{
    uint row = 0;
    for (PackedMatrix::iterator it = m.matrix.beginMatrix(); it != m.matrix.endMatrix(); ++it, row++) {
        cout << *it << " -- row:" << row;
        if (row >= m.num_rows)
            cout << " (considered past the end)";
        cout << endl;
    }
}

void Gaussian::print_last_one_in_cols(matrixset& m) const
{
    for (uint i = 0; i < m.num_cols; i++) {
        cout << "last_one_in_col[" << i << "]-1 = " << m.last_one_in_col[i]-1 << endl;
    }
}

const bool Gaussian::nothing_to_propagate(matrixset& m) const
{
    for(PackedMatrix::iterator r = m.matrix.beginMatrix(), end = m.matrix.endMatrix(); r != end; ++r) {
        if ((*r).popcnt_is_one()
            && solver.assigns[m.col_to_var[(*r).scan(0)]].isUndef())
            return false;
    }
    for(PackedMatrix::iterator r = m.matrix.beginMatrix(), end = m.matrix.endMatrix(); r != end; ++r) {
        if ((*r).isZero() && (*r).is_true())
            return false;
    }
    return true;
}

const bool Gaussian::check_last_one_in_cols(matrixset& m) const
{
    for(uint i = 0; i < m.num_cols; i++) {
        const uint last = std::min(m.last_one_in_col[i] - 1, (int)m.num_rows);
        uint real_last = 0;
        uint i2 = 0;
        for (PackedMatrix::iterator it = m.matrix.beginMatrix(); it != m.matrix.endMatrix(); ++it, i2++) {
            if ((*it)[i])
                real_last = i2;
        }
        if (real_last > last)
            return false;
    }
    
    return true;
}

void Gaussian::check_matrix_against_varset(PackedMatrix& matrix, const matrixset& m) const
{
    for (uint i = 0; i < matrix.getSize(); i++) {
        const PackedRow mat_row = matrix.getMatrixAt(i);
        const PackedRow var_row = matrix.getVarsetAt(i);
        
        unsigned long int col = 0;
        bool final = false;
        while (true) {
            col = var_row.scan(col);
            if (col == ULONG_MAX) break;
            
            const Var var = col_to_var_original[col];
            assert(var < solver.nVars());
            
            if (solver.assigns[var] == l_True) {
                assert(!mat_row[col]);
                assert(m.col_to_var[col] == unassigned_var);
                assert(m.var_is_set[var]);
                final = !final;
            } else if (solver.assigns[var] == l_False) {
                assert(!mat_row[col]);
                assert(m.col_to_var[col] == unassigned_var);
                assert(m.var_is_set[var]);
            } else if (solver.assigns[var] == l_Undef) {
                assert(m.col_to_var[col] != unassigned_var);
                assert(!m.var_is_set[var]);
                assert(mat_row[col]);
            } else assert(false);
            
            col++;
        }
        if ((final^!mat_row.is_true()) != !var_row.is_true()) {
            cout << "problem with row:"; print_matrix_row_with_assigns(var_row); cout << endl;
            assert(false);
        }
    }
}

const void Gaussian::check_first_one_in_row(matrixset& m, const uint j)
{
    if (j) {
        uint16_t until2 = std::min(m.last_one_in_col[m.least_column_changed] - 1, (int)m.num_rows);
        if (j-1 > m.first_one_in_row[m.num_rows-1]) {
            until2 = m.num_rows;
            #ifdef VERBOSE_DEBUG
            cout << "j-1 > m.first_one_in_row[m.num_rows-1]" << "j:" << j << " m.first_one_in_row[m.num_rows-1]:" << m.first_one_in_row[m.num_rows-1] << endl;
            #endif
        }
        for (uint i2 = 0; i2 != until2; i2++) {
            #ifdef VERBOSE_DEBUG
            cout << endl << "row " << i2 << " (num rows:" << m.num_rows << ")" << endl;
            cout << m.matrix.getMatrixAt(i2) << endl;
            cout << " m.first_one_in_row[m.num_rows-1]:" << m.first_one_in_row[m.num_rows-1] << endl;
            cout << "first_one_in_row:" << m.first_one_in_row[i2] << endl;
            cout << "num_cols:" << m.num_cols << endl;
            cout << "popcnt:" << m.matrix.getMatrixAt(i2).popcnt() << endl;
            cout << "popcnt_is_one():" << m.matrix.getMatrixAt(i2).popcnt_is_one() << endl;
            cout << "popcnt_is_one("<< m.first_one_in_row[i2] <<"): " << m.matrix.getMatrixAt(i2).popcnt_is_one(m.first_one_in_row[i2]) << endl;
            #endif
            
            for (uint i3 = 0; i3 < m.first_one_in_row[i2]; i3++) {
                assert(m.matrix.getMatrixAt(i2)[i3] == 0);
            }
            assert(m.matrix.getMatrixAt(i2)[m.first_one_in_row[i2]]);
            assert(m.matrix.getMatrixAt(i2).popcnt_is_one() ==
            m.matrix.getMatrixAt(i2).popcnt_is_one(m.first_one_in_row[i2]));
        }
    }
}

//old functions

/*void Gaussian::update_matrix_by_row(matrixset& m) const
{
#ifdef VERBOSE_DEBUG
    cout << "Updating matrix." << endl;
    uint num_updated = 0;
#endif
#ifdef DEBUG_GAUSS
    assert(nothing_to_propagate(cur_matrixset));
#endif

    mpz_class toclear, tocount;
    uint last_col = 0;

    for (uint col = 0; col < m.num_cols; col ++) {
        Var var = m.col_to_var[col];

        if (var != UINT_MAX && !solver.assigns[var].isUndef()) {
            toclear.setBit(col);
            if (solver.assigns[var].getBool()) tocount.setBit(col);

#ifdef DEBUG_GAUSS
            assert(m.var_to_col[var] < UINT_MAX-1);
#endif
            last_col = col;
            m.least_column_changed = std::min(m.least_column_changed, (int)col);

            m.removeable_cols++;
            m.col_to_var[col] = UINT_MAX;
            m.var_to_col[var] = UINT_MAX-1;
#ifdef VERBOSE_DEBUG
            num_updated++;
#endif
        }
    }

    toclear.invert();
    mpz_class tmp;
    mpz_class* this_row = &m.matrix[0];
    for(uint i = 0, until = std::min(m.num_rows, m.last_one_in_col[last_col]+1); i < until; i++, this_row++) {
        mpz_class& r = *this_row;
        mpz_and(tmp.get_mp(), tocount.get_mp(), r.get_mp());
        r.invert_is_true(tmp.popcnt() % 2);
        r &= toclear;
}

#ifdef VERBOSE_DEBUG
    cout << "Updated " << num_updated << " matrix cols. Could remove " << m.removeable_cols << " cols " <<endl;
#endif
}*/

/*void Gaussian::update_matrix_by_col(matrixset& m, const uint last_level) const
{
#ifdef VERBOSE_DEBUG
    cout << "Updating matrix." << endl;
    uint num_updated = 0;
#endif
#ifdef DEBUG_GAUSS
    assert(nothing_to_propagate(cur_matrixset));
#endif

    for (int level = solver.trail.size()-1; level >= last_level; level--){
        Var var = solver.trail[level].var();
        const uint col = m.var_to_col[var];
        if ( col < UINT_MAX-1) {
            update_matrix_col(m, var, col);
#ifdef VERBOSE_DEBUG
            num_updated++;
#endif
        }
    }

#ifdef VERBOSE_DEBUG
    cout << "Updated " << num_updated << " matrix cols. Could remove " << m.removeable_cols << " cols (out of " << m.num_cols << " )" <<endl;
#endif
}*/

}; //NAMESPACE MINISAT
