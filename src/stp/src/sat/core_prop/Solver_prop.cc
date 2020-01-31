/***************************************************************************************[Solver_prop.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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

/*
 *
 * This is a modified version of minisat 2.2 that has a propagator for function congruence built into the
 * normal propatate()/search() loop.
 */



#include <math.h>
#include <algorithm>

#include "../mtl/Sort.h"
#include "../core_prop/Solver_prop.h"

using namespace Minisat;

//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));


//=================================================================================================
// Constructor/Destructor:

Solver_prop::Solver_prop(volatile bool& timeout) :

    // Parameters (user settable):
    //
  aa_id(0)
  , last_id(-1)
  , number_of_arrays(0)
  , array_trail(0)
  , watched_indexes(0)
  , top_level_var(0)
  , alternate_trail_sorted_to(0)
  , val_to_aa(NULL)
  , verbosity        (0)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)

    // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (timeout)
{}


Solver_prop::~Solver_prop()
{
    delete[] val_to_aa;
    for (int i=0; i < (int)arrayData.size(); i++)
    {
            delete arrayData[i];
    }
}
//=================================================================================================
// Methods for the array propagator:

const bool debug_print = false;

bool
sortByLevel(const Minisat::Solver_prop::Assignment& a,
        const Minisat::Solver_prop::Assignment& b)
{
    return a.decisionLevel < b.decisionLevel;
}


// Literals that are l_Undef come first, then the rest are sorted by decreasing decision level.
void
Solver_prop::sortVecByLevel(vec<Lit> & c)
{
    LessThan_Level l(this);
    sort(c, l);
}

// Inplace sort of the alternate trail.
void
Solver_prop::sortAlternateTrail()
{
    int length = alternate_trail.size();
    assert(alternate_trail_sorted_to <= length);

    if (alternate_trail_sorted_to == length)
        return;

    std::sort(alternate_trail.begin()+alternate_trail_sorted_to, alternate_trail.end(), sortByLevel);
    std::inplace_merge(alternate_trail.begin(), alternate_trail.begin()+alternate_trail_sorted_to, alternate_trail.end(), sortByLevel);

    alternate_trail_sorted_to = length;
}


// array_id must grow monotonically.
// returns false if it's already a conflict.
bool
Solver_prop::addArray(int array_id, const vec<Lit>& i, const vec<Lit>& v, const vec<lbool>& ki, const vec<lbool>& kv)
{
    assert((i.size() > 0) ^ (ki.size() > 0));
    assert((v.size() > 0) ^ (kv.size() > 0));

    if (!ok) return false;

    if (i.size() > INDEX_BIT_WIDTH || ki.size() > INDEX_BIT_WIDTH)
        {
            printf("The array propagators unfortunately don't do arbitrary precision integers yet. "
                    "With the INDICES_128BITS compile time flag STP does 128-bits on 64-bit machines compiled with GCC. "
                    "Currently STP is compiled to use %d bit indices. "
                    "Unfortunately your problem has array indexes of size %d bits. "
                    "STP does arbitrary precision indices with the '--oldstyle-refinement' or the '-r' flags.\n",
                    INDEX_BIT_WIDTH, std::max(i.size(), ki.size()));
            exit(1);
        }


    bool startOfNewArray = false;
    if (array_id != last_id)
        {
            assert(array_id > last_id);
            number_of_arrays++;

            // Map doesn't have a copy constructor, so we create one on the heap.
            // Some constant indexes will already have been copied into the val_to_aa map.
            Map<index_type, std::vector<ArrayAccess*> >* t = new Map<index_type, std::vector<ArrayAccess*>  > [number_of_arrays];

            for (int j=0; j < number_of_arrays-1 ; j++)
                val_to_aa[j].moveTo(t[j]);

            delete[] val_to_aa;
            val_to_aa = t;
            last_id = array_id;
            startOfNewArray = true;
        }

    assert(number_of_arrays > 0);

    ArrayAccess * iv = new ArrayAccess(aa_id++,i,v,ki,kv, number_of_arrays-1);
    assert (!iv->known_index); // Not already added.

    if (!startOfNewArray)
        {
            assert(arrayData.last()->indexSize() == iv->indexSize());
            assert(arrayData.last()->valueSize() == iv->valueSize());
        }
    arrayData.push(iv);

    // Adds it into the map if the index is known.
    if (iv->isIndexConstant())
        {
            CRef r = writeOutArrayAxiom(*iv);
            if (r != CRef_Undef)
                {
                    ok = false;
                    return ok;
                }
            assert (iv->known_index); // No added.
        }
    else
        {
            int & ii = iv->index_index ;
            for (ii=0; ii < iv->indexSize(); ii++)
                {
                    if (value(iv->index[ii]) == l_Undef)
                    {
                            break;
                    }
               }
            if (ii < iv->indexSize())
                startWatchOfIndexVariable(iv);
            else
                {
                    // The index has been determined by unit propagation already.
                    // We can't add it to the watchlist yet though, because when
                    // we add it. It creates new variables. These variables might
                    // conflict with clauses that have yet to be added. So we
                    // need to save this and add it during solve().
                    iv->index_index = 0;
                    toAddAtStartup.push(iv);
                }
            assert (!iv->known_index); // No added.
        }
    return true;
}

// Assumes the index of the access has at least one unset variable.
void Solver_prop::startWatchOfIndexVariable(ArrayAccess* iv)
{
    assert(!iv->isIndexConstant());
    assert(!iv->known_index);
    assert(!IndexIsSet(*iv));
    const int indexSize = iv->indexSize();

    if (value(iv->index[iv->index_index]) != l_Undef)
        {
            // Loop around checking for the next unset index.

            int j;
            for (j = iv->index_index+1; j < indexSize; j++)
                if (value(iv->index[j]) == l_Undef)
                    break;

            if (j == indexSize)
                for (j = 0; j < indexSize; j++)
                    if (value(iv->index[j]) == l_Undef)
                        break;

            assert(j < indexSize);
            iv->index_index = j;
        }

    Var v = var(iv->index[iv->index_index]);
    assert (value(iv->index[iv->index_index]) == l_Undef);

    array_of_interest[v] = 1;
    if (!watchedLiterals.has(v))
        watchedLiterals.insert(v, std::vector<ArrayAccess*>());

    watchedLiterals[v].push_back(iv);
    watched_indexes++;
}


// Reads out the array index as an integer. It is completely specified.
index_type
Solver_prop::index_as_int(const ArrayAccess& iv)
{
    if (iv.isIndexConstant())
        return iv.constantIndex();

    index_type t = 0;
    assert(INDEX_BIT_WIDTH >= iv.indexSize());

    for (int i = 0; i < iv.indexSize(); i++)
        {
            lbool v = accessIndex(iv, i);
            assert(v == l_True || v == l_False);
            if (v == l_True)
                t += (1 << i);
        }

    return t;
}

// What is the value of iv->index[i]?
lbool
Solver_prop::accessIndex(const ArrayAccess& iv, int i)
{
    assert(i < iv.indexSize());
    assert(i >=0);
    if (iv.isIndexConstant())
        return iv.constant_index[i];
    return value(iv.index[i]);
}

lbool
Solver_prop::accessValue(const ArrayAccess& iv, int i)
{
    assert(i < iv.valueSize());
    assert(i >=0);
    if (iv.isValueConstant())
        return iv.constant_value[i];
    return value(iv.value[i]);
}


void Solver_prop::assertIndexesEqual(ArrayAccess &a, ArrayAccess &b)
{
    assert(a.indexSize() == b.indexSize());
    assert(a.array_id == b.array_id);
    for (int i=0; i < a.indexSize();i++)
        {
            assert(accessIndex(a,i) == accessIndex(b,i));
        }
}

const bool debug_equals_lit=false;

CRef
Solver_prop::addExtraClause(vec<Lit>& c)
{
    sortVecByLevel(c);
    CRef f = ca.alloc(c, false);
    clauses.push(f);
    attachClause(f);

    return f;
}


// Given two array accesses, builds up an equals formula for use on the lhs of an array axiom instance.
CRef Solver_prop::getEqualsLit( ArrayAccess &a,  ArrayAccess &b, Lit & result, bool& alreadyCreated)
{
    assert(&a != &b);
    assert(a.id != b.id); // Can't compare the same accesses.
    assert(a.array_id == b.array_id);
    assertIndexesEqual(a, b);
    assert(IndexIsSet(a));

    const int indexSize = a.indexSize();

    alreadyCreated = false;

    {
        ArrayAccess& lookup = (a.id < b.id) ? a : b;
        ArrayAccess& other =  (a.id < b.id) ? b : a;
        EqualityVariables evss(lookup.id, other.id);

        // Lookup the already created equality variables. Maybe we've created it already.
        if (equality_variables.peek(evss,result))
            {
                alreadyCreated = true;
                assert(value(result) == l_True);
                return CRef_Undef;
            }

        // Create the result variable. Store so we can reuse later.
          result = mkLit(newVar(false,true),false);
          equality_variables.insert(evss, result);
    }

    if (a.isIndexConstant() && b.isIndexConstant())
        {
            // We know already they are equal.
            assert(decisionLevel() == 0);
            uncheckedEnqueue(result);
            return propagate();
        }

     vec<Lit> clause;
     clause.capacity(indexSize+1);
     clause.push(result);

     if (a.isIndexConstant() || b.isIndexConstant())
        {
            ArrayAccess & constantIndex = a.isIndexConstant()? a:b;
            ArrayAccess & other = a.isIndexConstant()? b:a;

            // Because one of the indexes is completely known (at decision level 0),
            // we include the other one in the clause.
            for (int i = 0; i < indexSize; i++)
            {
                    if (accessIndex(constantIndex,i) == l_True)
                        clause.push(~other.index[i]);
                    else
                        clause.push(other.index[i]);
            }
        }
    else
        {
            assert (!a.isIndexConstant());
            assert (!b.isIndexConstant());

            for (int i=0; i < indexSize;i++)
                clause.push(mkLit(newVar(false,true),true));

            // Add clauses for 1,1 => true, and 0,0 => true.
            for (int i = 0; i < indexSize; i++)
            {
                assert (accessIndex(a,i) == accessIndex(b,i));
                assert (accessIndex(a,i) != l_Undef);

                // One of these two is used to set the intermediate value.
                eqLitHelper(~a.index[i], ~b.index[i], ~clause[i+1]);
                eqLitHelper(a.index[i], b.index[i], ~clause[i+1]);
            }
        }
    assert((int)clause.size() == (indexSize+1));

    #ifndef NDEBUG
        int lvl =0;
        for (int i=1; i <= indexSize;i++)
        {
            lvl = std::max(lvl,level(var(clause[i])));
            // All the immediates should now be true.
            // But we store the "Not" of them into the clause..
            assert(value(clause[i]) == l_False);
        }
        assert(lvl == decisionLevel());
    #endif

    CRef from = addExtraClause(clause);
    uncheckedEnqueue(result, from);
    assert(value(result) == l_True);

    return propagate();
}

void
Solver_prop::eqLitHelper(const Lit& l0, const Lit& l1, const Lit& intermed)
{
    vec<Lit> c;
    c.push(intermed);
    c.push(l0);
    c.push(l1);
    CRef f = addExtraClause(c);

    // It's only when l0 and l1 are false that anything more happens.
    if (value(l0) == l_False)
        {
            assert(value(l1) == l_False);
            assert(value(intermed) == l_Undef);

            int lvl = std::max(level(var(l0)),level(var(l1)));
            assert (lvl <= decisionLevel());

            assigns[var(intermed)] = l_True;
            vardata[var(intermed)] = mkVarData(f, lvl);

            assert((ca[f][0])==intermed);

            for (int i=1; i < c.size();i++)
                {
                    assert (value(ca[f][i]) == l_False);
                    assert ((level(var(ca[f][i]))) <= lvl);
                }

            alternate_trail.push_back(Assignment(intermed, lvl));
            assert(level(var(intermed)) == lvl);
            assert(watches[intermed].size() ==0);
        }
    return ;
}

// Index is completely known.
bool Solver_prop::IndexIsSet(const ArrayAccess& iv)
{
        if (iv.isIndexConstant())
                return true;

        for (int i=0; i < iv.indexSize();i++)
        {
                if (value(iv.index[i]) == l_Undef)
                        return false;
        }
        return true;
}

void
Solver_prop::printClauses()
{
    for (int i = 0; i < clauses.size(); i++)
        {
            const Clause &c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                {
                    printf("%c%d[%c:%d] ", sign(c[j]) ? '-' : ' ', var(c[j]), printValue(value(c[j])), level(var(c[j])));
                }
            printf("\n");
        }
}

// Assuming the index is known. Add the clauses to enforce that
// it's the same as the zeroeth array access with the same index.
CRef
Solver_prop::writeOutArrayAxiom(ArrayAccess& iv)
{
    assert(IndexIsSet(iv));

    const index_type asInt = index_as_int(iv);

    if (!val_to_aa[iv.array_id].has(asInt))
        val_to_aa[iv.array_id].insert(asInt, std::vector<ArrayAccess*>());

    std::vector<ArrayAccess*>& aa = val_to_aa[iv.array_id][asInt];

    bool alreadyAdded = false; // Already in the bucket with the other values with the same index??

    for (int j = 0; j < (int) aa.size(); j++)
        if (&iv == aa[j])
            {
                assert(!alreadyAdded); // only once.
                assert(index_as_int(iv) == asInt);
                alreadyAdded = true;
            }

    if (!alreadyAdded)
        {
            assert(!iv.known_index);

            aa.push_back(&iv);

            if (arrayHistory_stack.size() > 0)
            {
                assert(arrayHistory_stack.last().decisionLevel <= decisionLevel());
            }


            // So it can be removed when we cancel.
            ArrayHistory h(&iv, decisionLevel());
            arrayHistory_stack.push(h);

            iv.known_index = true;
        }

    if (aa.size() == 1)
        return CRef_Undef;

    bool alreadyCreated = false; // Are the clauses constraining them in there.

    ArrayAccess& aa_0 = *aa[0];
    ArrayAccess& aa_back = *aa.back();

    Lit eq;
    CRef conflict = getEqualsLit(aa_0, aa_back, eq, alreadyCreated);

    if (alreadyCreated)
        return CRef_Undef; // All the clauses have been created already for these guys.

    assert(value(eq) == l_True);
    // Add the rhs of the equality.

    vec<Lit> c;

    for (int i = 0; i < iv.valueSize(); i++)
        {
            c.clear();
            c.push(~eq);

            lbool a0_v = accessValue(aa_0,i);
            lbool aback_v = accessValue(aa_back,i);

            CRef f;

            if (aa_0.isValueConstant() && aa_back.isValueConstant())
                {
                    if (a0_v != aback_v)
                        {
                            return ca.alloc(c);
                        }
                        else
                            continue;
                }
            else if (aa_0.isValueConstant())
                {
                    assert (a0_v != l_Undef);

                    if (a0_v == l_True)
                        c.push(aa_back.value[i]);
                    else
                        c.push(~aa_back.value[i]);
                }
            else if (aa_back.isValueConstant())
                {
                    assert (aback_v != l_Undef);

                    if (aback_v == l_True)
                        c.push(aa_0.value[i]);
                    else
                        c.push(~aa_0.value[i]);
                }
            else
                {
                    c.push(aa_0.value[i]);
                    c.push(~(aa_back.value[i]));

                    f = addExtraClause(c);

                    assert(ca[f].size() ==3);
                    if ((value(ca[f][1]) == l_False) && (value(ca[f][2]) == l_False))
                        {
                            const lbool first=  value(ca[f][0]);
                            if (first == l_Undef)
                                uncheckedEnqueue(ca[f][0], f);
                            else if (first == l_False)
                                conflict = f;
                        }

                    c.clear();
                    c.push(~eq);
                    c.push(~aa_0.value[i]);
                    c.push(aa_back.value[i]);
                }

            f = addExtraClause(c);
            const Clause& newC = ca[f];

            bool restFalse = true;
            for (int j=1; j< newC.size();j++)
            {
                if (value(newC[j]) != l_False)
                {
                        restFalse = false;
                        break;
                }
            }

            bool conflicted=false;
            if (restFalse)
                {
                    if (value(newC[0]) == l_Undef)
                         uncheckedEnqueue(newC[0],f);
                    else if (value(newC[0]) == l_False)
                        conflicted=true;
                }


            // We save up the conflicts because we want all of the clauses to be added.
            if (conflicted)
                {
                    int maxLevel=0;
                    if (!aa_0.isValueConstant())
                        maxLevel = level(var(aa_0.value[i]));

                    if (!aa_back.isValueConstant())
                        maxLevel = std::max(level(var(aa_back.value[i])),maxLevel);

                    if (maxLevel ==0)
                        {
                            c.clear();
                            c.push(~eq);
                            return ca.alloc(c);
                        }

                    conflict = f;
                }
        }


    CRef rr = propagate();
    if (rr!=CRef_Undef)
        conflict = rr;

    return conflict;
}

// Look through each of the variables that have been set and see if they watch variables on array indexes.
CRef Solver_prop::arrayPropagate()
{
    if (watched_indexes ==0)
        {
            // either there are no arrays, or,
            array_trail = trail.size();
            return CRef_Undef;
        }

    for (; array_trail < trail.size(); array_trail++)
        {
            // check whether we are interested in any of the literals in the trail.
            Var trail_variable = var(trail[array_trail]);
            if (array_of_interest[trail_variable])
                {
                    Var variable = var(trail[array_trail]);
                    assert(watchedLiterals.has(variable));

                    // Initially I had this v as a reference. However, this instance is contained in a map, that can be rehashed and hence the vector moved around
                    // in memory (causing the reference to point to memory that no longer contains the vector.
                    std::vector<ArrayAccess*> v = watchedLiterals[variable]; // Take a copy.
                    assert(v.size() >0);
                    int initial_vector_size = (int)v.size(); // because more can be added in by the startWatchOfIndexVariable function.

                    for (int i=0; i < (int)initial_vector_size;i++)
                    {
                            watched_indexes--;
                            ArrayAccess& iv = *(v[i]);

                            assert(!iv.known_index); // Not already added.
                            assert(!iv.isIndexConstant()); // Completely known. So it should be in the map already.
                            assert(iv.indexSize() > 0);

                            assert(var(iv.index[iv.index_index]) == trail_variable);
                            assert(value(iv.index[iv.index_index]) != l_Undef);

                            // Checks each of the indexes around the loop!!.
                            int end = ((iv.index_index == 0)? iv.indexSize()-1 : iv.index_index-1);
                            bool first = true; // so 1-bit indexes are checked.
                            for (; (iv.index_index != end) || first ; iv.index_index = ((iv.index_index+1) % iv.indexSize()))
                            {
                                    assert(iv.index_index < iv.indexSize());

                                    lbool val = value(iv.index[iv.index_index]);
                                    if (val == l_Undef)
                                            break;
                                    first = false;
                            }
                            assert(iv.index_index < iv.indexSize());

                            if (iv.index_index == end && l_Undef != value(iv.index[iv.index_index]))
                            {
                                    //All of the bits are set to either true or false.
                                    for (int w=0; w< iv.indexSize();w++)
                                        {
                                            assert(value(iv.index[w]) != l_Undef);
                                        }

                                    CRef r = writeOutArrayAxiom(iv);
                                    if (r != CRef_Undef)
                                        {
                                            std::vector<ArrayAccess*>& vec = watchedLiterals[variable];
                                            assert(vec.size() >= v.size());
                                            vec.erase(vec.begin(), vec.begin()+i+1);

                                            if(vec.size() ==0)
                                                {
                                                    watchedLiterals.remove(variable);
                                                    array_of_interest[variable] = 0;
                                                }
                                            return r;
                                        }

                                    assert(iv.known_index);
                            }
                            else
                                {
                                    assert (value(iv.index[iv.index_index])  == l_Undef);
                                    startWatchOfIndexVariable(&iv);
                                    assert (!iv.known_index); // Not already added.
                                }
                    }

                    std::vector<ArrayAccess*>& vec = watchedLiterals[variable]; // Reference.
                    assert(vec.size() >= v.size());

                    if((int)vec.size() == initial_vector_size)
                        {
                            //
                            watchedLiterals.remove(variable);
                            array_of_interest[variable] = 0;
                        }
                    else
                        {
                            vec.erase(vec.begin(),vec.begin() + initial_vector_size);
                        }
                }
        }
    return CRef_Undef;
  }

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver_prop::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    array_of_interest.push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}


bool Solver_prop::addClause_(vec<Lit>& ps)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    if (ps.size() == 0)
        return ok = false;
    else if (ps.size() == 1){
    	 uncheckedEnqueue(ps[0]);
        return ok = (propagate() == CRef_Undef);
    }else{
        CRef cr = ca.alloc(ps, false);
        clauses.push(cr);
        attachClause(cr);
    }

    return true;
}


void Solver_prop::attachClause(CRef cr) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }


void Solver_prop::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }


void Solver_prop::removeClause(CRef cr) {
    Clause& c = ca[cr];
    detachClause(cr);
    // Don't leave pointers to free'd memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    c.mark(1); 
    ca.free(cr);
}


bool Solver_prop::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at given level (keeping all assignment at 'level' but not beyond).
//
void Solver_prop::cancelUntil(int level) {
	if (decisionLevel() > level){

	struct to_re_add
	{
	    index_type index_value;
	    int array_id;
	};

	vec<index_type> toRep;
	vec<ArrayAccess*> aaRep;

	vec<ArrayAccess*> toReAdd;

        // look through the map, and remove it.
        while ((arrayHistory_stack.size() > 0) && (arrayHistory_stack.last().decisionLevel > level))
        {
        	ArrayAccess& aa = *(arrayHistory_stack.last().aa);
                assert(aa.known_index);
                assert(!aa.isIndexConstant()); // Shouldn't remove known indexes.
                assert(IndexIsSet(aa));   // The index shouldn't be unset yet.

        	// Get the integer.
                index_type asInt = index_as_int(aa);
        	assert(val_to_aa[aa.array_id].has(asInt));

        	std::vector<ArrayAccess*>& aaV = val_to_aa[aa.array_id][asInt];

        	// We'll remove the zeroeth array access, so need to re-add all of the array axioms.
                if (aaV[0] == &aa)
                    {
                        toRep.push(asInt);
                        aaRep.push(&aa);
                    }

                bool found = false;
                for (int i = 0; i < (int) aaV.size(); i++)
                    if (aaV[i] == &aa)
                        {
                            //Find the same pointer and erase it.
                            aaV.erase(aaV.begin() + i);
                            found = true;
                            break;
                        }
                assert(found);

                    if (aaV.size() == 0)
                        val_to_aa[aa.array_id].remove(asInt);

                    aa.known_index = false;
                    toReAdd.push(&aa);
                    arrayHistory_stack.shrink(1);
                }

	// The zeroeth of these numbers has been deleted, so we might need to redo the implications.
	for (int i=0; i < toRep.size(); i++)
	{
	        index_type asInt = toRep[i];
	        ArrayAccess& aa = *aaRep[i];

	        if (val_to_aa[aa.array_id].has(asInt))
	            {

	                std::vector<ArrayAccess*>& aaV = val_to_aa[aa.array_id][asInt];
	                for (int j=1;j<(int)aaV.size();j++)
	                {
	                        assert(aa.known_index);
	                        writeOutArrayAxiom(*aaV[j]);
	                }
	            }
	}

	sortAlternateTrail();
        while (alternate_trail.size() > 0 && (alternate_trail.back().decisionLevel > level))
            {
                Var x = var( alternate_trail.back().l);
                assigns [x] = l_Undef;
                alternate_trail.erase(alternate_trail.end()-1);
            }
        alternate_trail_sorted_to = alternate_trail.size();

        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        trail_lim.shrink(trail_lim.size() - level);

        for (int i=0; i < toReAdd.size(); i++)
            {
                ArrayAccess* aa = toReAdd[i];
                startWatchOfIndexVariable(aa);
            }

        array_trail = std::min(trail.size(), array_trail);
	}
}


//=================================================================================================
// Major methods:


Lit Solver_prop::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
            next = order_heap.removeMin();

    return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|  
|  Description:
|    Analyze conflict and produce a reason clause.
|  
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|  
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the 
|        rest of literals. There may be others from the same level though.
|  
|________________________________________________________________________________________________@*/
void Solver_prop::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel)
{
    int pathC = 0;
    Lit p     = lit_Undef;


    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    // If this is false, then we don't need to check the alternate_trail.
    bool bigFound =false;

#ifndef NDEBUG
    // The conflict needs to be discovered before additional decisions are made.
    int max_level2 =0;
    Clause& c1 = ca[confl];
    for (int j=0; j < c1.size();j++)
        {
            if (max_level2 < level(var(c1[j])))
                max_level2 = level(var(c1[j]));
        }

    assert (max_level2 == decisionLevel());
#endif

    if (debug_print)
        {
            printf("!!starting %d\n", decisionLevel());
            printf("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
        }
    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt())
            claBumpActivity(c);

        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));
                seen[var(q)] = 1;

                if (toInt(var(q)) >= top_level_var)
                    bigFound=true;

                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }
        
        p  = lit_Undef;

        // This looks for the literal in either of the watchlists with the highest level. It's slow because
        // in the worst case it will iterate completely through both lists. strcmp32.c.smt is much slower
        // because of this implementation.. However most of the time alternate_trail is small because it
        // only grown when a new intermediate variable is added. That variable is only added once, and
        // is removed when the level it was set at is Cancelled below.
        if (bigFound && alternate_trail.size() > 0)
                {
                    sortAlternateTrail();

                    int unset_index = alternate_trail.size() - 1;
                    while (unset_index >= 0 && !seen[(var(alternate_trail[unset_index].l))])
                        unset_index--;

                    if (unset_index >= 0)
                        p = alternate_trail[unset_index].l;
                    if (debug_print && p != lit_Undef)
                        printf("Found unsat var: %d\n", var(p));

                }


        if (p == lit_Undef)
        {
            while (!seen[var(trail[index--])]);
            p     = trail[index+1];

            if (debug_print && p != lit_Undef)
                printf("(1) Found trail var: %d\n", var(p));

        }
        else
            {
                int t_index = index;
                while (t_index>=  0 && !seen[var(trail[t_index--])]);
                if (t_index >= 0)
                    {
                        if (debug_print)
                            printf("::%d %d\n", level(var(p)) , level(var(trail[t_index+1])));

                        if (level(var(p)) < level(var(trail[t_index+1])))
                            {
                                p     = trail[t_index+1];
                                index = t_index;
                            }
                    }
                if (debug_print && p != lit_Undef)
                    printf("(2) Found trail var: %d\n", var(p));

            }


        confl = reason(var(p));
        seen[var(p)] = 0;
        if (debug_print)
            printf("Var %d, pathC %d, level %d, isUndef %d\n",toInt(var(p)),pathC, level(var(p)), (reason(var(p)) == CRef_Undef));
        pathC--;

        if (pathC >0)
            {
                assert(confl != CRef_Undef); // (otherwise should be UIP)

                if (debug_print)
                    printf("%d %d\n", toInt(p), toInt(var(p)));
                Minisat::Clause  cl= ca[confl];

                assert(ca[confl][0] ==p);
                assert(value(p) != l_Undef);
            }

        if (debug_print)
        {
            printf("Learnt Clauses:\n");
            printClause(out_learnt);
        }
    }while (pathC > 0);
    out_learnt[0] = ~p;

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level))
                out_learnt[j++] = out_learnt[i];
        
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    }else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)
}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver_prop::litRedundant(Lit p, uint32_t abstract_levels)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    while (analyze_stack.size() > 0){
        assert(reason(var(analyze_stack.last())) != CRef_Undef);
        Clause& c = ca[reason(var(analyze_stack.last()))]; analyze_stack.pop();

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver_prop::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver_prop::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef); // Shouldn't be set already.
    if (from != CRef_Undef)
        {
            assert((ca[from][0])==(p));

            const Clause& c = ca[from];
            for (int i=1; i < c.size();i++)
                {
                    assert (value(c[i]) != l_Undef);
                    assert ((level(var(c[i]))) <= decisionLevel());
                }
        }

    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    //
    //printf("Enqueu %d with reasons %c %d\n", var(p), from == CRef_Undef?'u':'c', decisionLevel());
    trail.push_(p);

    if (from != CRef_Undef)
        {
            assert(ca[from][0] == p);
        }

    if (false &&from != CRef_Undef)
        {
            Clause& c = ca[from];
            for (int i = 0; i < c.size(); i++)
                {
                    printf("%c", printValue(value(c[i])));
                }
            printf("\n");
        }
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver_prop::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();

    while (qhead < trail.size()){
        Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
        vec<Watcher>&  ws  = watches[p];
        Watcher        *i, *j, *end;
        num_props++;

        for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
            // Try to avoid inspecting the clause:
            Lit blocker = i->blocker;
            if (value(blocker) == l_True){
                *j++ = *i++; continue; }

            // Make sure the false literal is data[1]:
            CRef     cr        = i->cref;
            Clause&  c         = ca[cr];
            Lit      false_lit = ~p;
            if (c[0] == false_lit)
                c[0] = c[1], c[1] = false_lit;
            assert(c[1] == false_lit);
            i++;

            // If 0th watch is true, then clause is already satisfied.
            Lit     first = c[0];
            Watcher w     = Watcher(cr, first);
            if (first != blocker && value(first) == l_True){
                *j++ = w; continue; }

            // Look for new watch:
            for (int k = 2; k < c.size(); k++)
                if (value(c[k]) != l_False){
                    c[1] = c[k]; c[k] = false_lit;
                    watches[~c[1]].push(w);
                    goto NextClause; }

            // Did not find watch -- clause is unit under assignment:
            *j++ = w;
            if (value(first) == l_False){
                confl = cr;
                qhead = trail.size();
                // Copy the remaining watches:
                while (i < end)
                    *j++ = *i++;
            }else
            	uncheckedEnqueue(first, cr);

        NextClause:;
        }
        ws.shrink(i - j);
    }
    propagations += num_props;
    simpDB_props -= num_props;

    return confl;
}



/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        return ca[x].size() > 2 && (ca[y].size() == 2 || ca[x].activity() < ca[y].activity()); } 
};
void Solver_prop::reduceDB()
{
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
}


void Solver_prop::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (satisfied(c))
            removeClause(cs[i]);
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}


void Solver_prop::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}


/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver_prop::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:
    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.
        removeSatisfied(clauses);
    checkGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assigment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver_prop::search(int nof_conflicts)
{
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;

    for (;;){
        CRef confl = propagate();
        if (confl== CRef_Undef)
            confl = arrayPropagate();


        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 0) return l_False;

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level);
             cancelUntil(backtrack_level);
             if (debug_print)
                 {
                     printClause(learnt_clause);
                     printf("Backtrack %d\n", backtrack_level);
                 }
             assert(value(learnt_clause[0]) == l_Undef);

            if (learnt_clause.size() == 1){
            	uncheckedEnqueue(learnt_clause[0]);
            }else{
                CRef cr = ca.alloc(learnt_clause, true);
                learnts.push(cr);
                attachClause(cr);
                claBumpActivity(ca[cr]);
                uncheckedEnqueue(learnt_clause[0], cr);
            }

            varDecayActivity();
            claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity >= 1)
                    printf("| %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

        }else{
            // NO CONFLICT
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts || !withinBudget()){
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(0);
                return l_Undef; }

            // Simplify the set of problem clauses:
            if (decisionLevel() == 0 && !simplify())
                return l_False;

            if (learnts.size()-nAssigns() >= max_learnts)
                // Reduce the set of learnt clauses:
                reduceDB();

            Lit next = lit_Undef;
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }

            if (next == lit_Undef){
                // New variable decision:
                decisions++;
                next = pickBranchLit();

                if (next == lit_Undef)
                    // Model found:
                    return l_True;
            }

            // Increase decision level and enqueue 'next'
            newDecisionLevel();
            uncheckedEnqueue(next);
        }
    }
}


double Solver_prop::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}

// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver_prop::solve_()
{
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    top_level_var = nVars();

    for (int i = 0; i < toAddAtStartup.size(); i++)
        {
            ArrayAccess* iv = toAddAtStartup[i];
            CRef r = writeOutArrayAxiom(*iv);
            if (r != CRef_Undef)
                {
                    ok = false;
                    return l_False;
                }
        }
    toAddAtStartup.clear();


    solves++;

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity >= 1){
        printf("============================[ Search Statistics ]==============================\n");
        printf("| Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("|           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
        status = search(rest_base * restart_first);
        if (!withinBudget()) break;
        curr_restarts++;
    }

    if (verbosity >= 1)
        printf("===============================================================================\n");


    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);

        assert(watched_indexes==0);
    }else if (status == l_False && conflict.size() == 0)
        ok = false;

    cancelUntil(0);
    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}


void Solver_prop::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}


void Solver_prop::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}


void Solver_prop::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 0)
        printf("Wrote %d clauses with %d variables.\n", cnt, max);
}


//=================================================================================================
// Garbage Collection methods:

void Solver_prop::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }

    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++)
        ca.reloc(learnts[i], to);

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
        ca.reloc(clauses[i], to);
}


void Solver_prop::garbageCollect()
{

    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    assert(ca.wasted() <= ca.size());
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("|  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
