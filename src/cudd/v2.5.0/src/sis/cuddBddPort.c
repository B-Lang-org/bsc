/**CFile***********************************************************************

  FileName    [cuddBddPort.c]

  PackageName [cudd]

  Synopsis    [SIS interface to the Decision Diagram Package of the
  University of Colorado.]

  Description [This file implements an interface between the functions in
    the Berkeley BDD package and the functions provided by the CUDD (decision
    diagram) package from the University of Colorado. The CUDD package is a
    generic implementation of a decision diagram data structure. For the time
    being, only Boole expansion is implemented and the leaves in the
    in the nodes can be the constants zero, one or any arbitrary value.]

  Author      [Abelardo Pardo]

  Copyright   [Copyright (c) 1994-1996 The Univ. of Colorado.
  All rights reserved.

  Permission is hereby granted, without written agreement and without license
  or royalty fees, to use, copy, modify, and distribute this software and its
  documentation for any purpose, provided that the above copyright notice and
  the following two paragraphs appear in all copies of this software.

  IN NO EVENT SHALL THE UNIVERSITY OF COLORADO BE LIABLE TO ANY PARTY FOR
  DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR CONSEQUENTIAL DAMAGES ARISING OUT
  OF THE USE OF THIS SOFTWARE AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF
  COLORADO HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

  THE UNIVERSITY OF COLORADO SPECIFICALLY DISCLAIMS ANY WARRANTIES,
  INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND
  FITNESS FOR A PARTICULAR PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN
  "AS IS" BASIS, AND THE UNIVERSITY OF COLORADO HAS NO OBLIGATION TO PROVIDE
  MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR MODIFICATIONS.]

******************************************************************************/

#include "util.h"
#include "array.h"
#include "st.h"

#ifdef EXTERN
#undef EXTERN
#endif
#define EXTERN
#include "cuddInt.h"
#include "cuddBdd.h"


/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

struct bdd_gen {
    bdd_manager *manager;
    DdGen	*ddGen;
    array_t	*cube;
};

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

#ifndef lint
static char rcsid[] DD_UNUSED = "$Id: cuddBddPort.c,v 1.11 1996/05/08 06:13:08 fabio Exp $";
#endif

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static bdd_t * bdd_construct_bdd_t (DdManager *mgr, DdNode * fn);

/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Terminates the bdd package.]

  SideEffects []

******************************************************************************/
void
bdd_end(mgr)
bdd_manager *mgr;
{
    if (mgr->hooks != NULL) FREE(mgr->hooks);
    Cudd_Quit(mgr);

} /* end of bdd_end */


/**Function********************************************************************

  Synopsis    [Initialize manager with the options given in mgr_init.]

  SideEffects []

******************************************************************************/
void
bdd_set_mgr_init_dflts(mgr_init)
bdd_mgr_init *mgr_init;
{
    fprintf(stderr,"CU DD Package: bdd_set_mgr_init_dflts translated to no-op\n");
    return;

} /* end of bdd_set_mgr_init_dflts */


/**Function********************************************************************

  Synopsis    [Starts the manager with nvariables variables.]

  SideEffects []

******************************************************************************/
bdd_manager *
bdd_start(nvariables)
int nvariables;
{
    DdManager *mgr;
    bdd_external_hooks *hooks;

    mgr =  Cudd_Init((unsigned int)nvariables,0,CUDD_UNIQUE_SLOTS,
		     CUDD_CACHE_SLOTS,0);

    hooks = ALLOC(bdd_external_hooks,1);
    hooks->mdd = hooks->network = hooks->undef1 = (char *) 0;
    mgr->hooks = (char *) hooks;

    return (bdd_manager *)mgr;

} /* end of bdd_start */


/**Function********************************************************************

  Synopsis    [Starts the manager with parameters.]

  SideEffects []

******************************************************************************/
bdd_manager *
bdd_start_with_params(nvariables, mgr_init)
int nvariables;
bdd_mgr_init *mgr_init;
{
    fprintf(stderr,"CU DD Package: bdd_start_with_parameters bypassed\n");
    return (bdd_manager *)Cudd_Init((unsigned int)nvariables,0,
	CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);

} /* end of bdd_start_with_params */


/**Function********************************************************************

  Synopsis    [Creates a new variable in the manager.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_create_variable(mgr)
bdd_manager *mgr;
{
    DdNode *var;
    DdManager *dd = (DdManager *) mgr;
    DdNode *one = DD_ONE(dd);

    if (dd->size >= CUDD_MAXINDEX -1) return(NULL);
    do {
	dd->reordered = 0;
	var = cuddUniqueInter(dd,dd->size,one,Cudd_Not(one));
    } while (dd->reordered == 1);

    if (var == NULL) return(NULL);
    cuddRef(var);
    return(bdd_construct_bdd_t(dd,var));

} /* end of bdd_create_variable */


/**Function********************************************************************

  Synopsis    [Creates a new variable and positions it after the
  variable with the specified index.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_create_variable_after(mgr, after_id)
bdd_manager *mgr;
bdd_variableId after_id;
{
    DdNode *var;
    DdManager *dd = (DdManager *) mgr;
    int level;

    if (after_id >= dd->size) return(NULL);
    level = 1 + dd->perm[after_id];
    var = Cudd_bddNewVarAtLevel(dd,level);
    if (var == NULL) return(NULL);
    cuddRef(var);
    return(bdd_construct_bdd_t(dd,var));

} /* end of bdd_create_variable_after */


/**Function********************************************************************

  Synopsis    [Returns the BDD representing the variable with given ID.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_get_variable(mgr, variable_ID)
bdd_manager *mgr;
bdd_variableId variable_ID;	       /* unsigned int */
{
    DdNode *var;
    DdManager *dd = (DdManager *) mgr;
    DdNode *one = DD_ONE(dd);

    if (variable_ID >= CUDD_MAXINDEX -1) return(NULL);
    do {
	dd->reordered = 0;
	var = cuddUniqueInter(dd,(int)variable_ID,one,Cudd_Not(one));
    } while (dd->reordered == 1);

    if (var == NULL) return(NULL);
    cuddRef(var);
    return(bdd_construct_bdd_t(dd,var));

} /* end of bdd_get_variable */


/**Function********************************************************************

  Synopsis    [Creates a copy of the BDD.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_dup(f)
bdd_t *f;
{
    cuddRef(f->node);
    return(bdd_construct_bdd_t((DdManager *)f->mgr,f->node));

} /* end of bdd_dup */


/**Function********************************************************************

  Synopsis    [Deletes the BDD of f.]

  SideEffects []

******************************************************************************/
void
bdd_free(f)
bdd_t *f;
{
    if (f == NULL) {
	fail("bdd_free: trying to free a NULL bdd_t");
    }

    if (f->free == TRUE) {
	fail("bdd_free: trying to free a freed bdd_t");
    }

    Cudd_RecursiveDeref((DdManager *)f->mgr,f->node);
    /* This is a bit overconservative. */
    f->node = 0;
    f->mgr = 0;
    f->free = 0;
    FREE(f);
    return;

} /* end of bdd_free */


/**Function********************************************************************

  Synopsis    [And of two BDDs.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_and(f, g, f_phase, g_phase)
bdd_t *f;
bdd_t *g;
boolean f_phase;
boolean g_phase;
{
    DdManager *dd;
    DdNode *newf,*newg,*fandg;
    bdd_t *result;

    /* Make sure both BDDs belong to the same manager. */
    assert(f->mgr == g->mgr);

    /* Modify the phases of the operands according to the parameters. */
    if (!f_phase) {
	newf = Cudd_Not(f->node);
    } else {
	newf = f->node;
    }
    if (!g_phase) {
	newg = Cudd_Not(g->node);
    } else {
	newg = g->node;
    }

    /* Perform the AND operation */
    dd = (DdManager *)f->mgr;
    fandg = Cudd_bddAnd((DdManager *)f->mgr,newf,newg);
    if (fandg == NULL) return(NULL);
    cuddRef(fandg);
    result = bdd_construct_bdd_t(dd,fandg);

    return(result);

} /* end of bdd_and */


/**Function********************************************************************

  Synopsis    [Abstracts variables from the product of two BDDs.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_and_smooth(f, g, smoothing_vars)
bdd_t *f;
bdd_t *g;
array_t *smoothing_vars;	/* of bdd_t *'s */
{
    int i;
    bdd_t *variable;
    DdNode *cube,*tmpDd,*result;
    DdManager *mgr;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == g->mgr);

    /* The Boulder package needs the smothing variables passed as a cube.
    ** Therefore we must build that cube from the indices of variables
    ** in the array before calling the procedure.
    */
    mgr = (DdManager *)f->mgr;
    Cudd_Ref(cube = DD_ONE(mgr));
    for (i = 0; i < array_n(smoothing_vars); i++) {
	variable = array_fetch(bdd_t *,smoothing_vars,i);

	/* Make sure the variable belongs to the same manager. */
	assert(mgr == variable->mgr);

        tmpDd = Cudd_bddAnd(mgr,cube,variable->node);
	if (tmpDd == NULL) {
	    Cudd_RecursiveDeref(mgr,cube);
	    return(NULL);
	}
        cuddRef(tmpDd);
	Cudd_RecursiveDeref(mgr, cube);
	cube = tmpDd;
    }

    /* Perform the smoothing */
    result = Cudd_bddAndAbstract(mgr,f->node,g->node,cube);
    if (result == NULL) {
	Cudd_RecursiveDeref(mgr, cube);
	return(NULL);
    }
    cuddRef(result);
    /* Get rid of temporary results. */
    Cudd_RecursiveDeref(mgr, cube);

    /* Build the bdd_t structure for the result */
    return(bdd_construct_bdd_t(mgr,result));

} /* end of bdd_and_smooth */


/**Function********************************************************************

  Synopsis    [Return a minimum size BDD between bounds.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_between(f_min, f_max)
bdd_t *f_min;
bdd_t *f_max;
{
    bdd_t *temp, *ret;

    temp = bdd_or(f_min, f_max, 1, 0);
    ret = bdd_minimize(f_min, temp);
    bdd_free(temp);
    return(ret);

} /* end of bdd_between */


/**Function********************************************************************

  Synopsis    [Computes the cofactor of f with respect to g.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_cofactor(f, g)
bdd_t *f;
bdd_t *g;
{
    DdNode *result;

    /* Make sure both operands belong to the same manager */
    assert(f->mgr == g->mgr);

    /* We use Cudd_bddConstrain instead of Cudd_Cofactor for generality. */
    result = Cudd_bddConstrain((DdManager *)f->mgr,f->node,g->node);
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t((DdManager *)f->mgr,result));

} /* end of bdd_cofactor */


/**Function********************************************************************

  Synopsis    [Functional composition of a function by a variable.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_compose(f, v, g)
bdd_t *f;
bdd_t *v;
bdd_t *g;
{
    DdNode *result;

    /* Make sure all operands belong to the same manager. */
    assert(f->mgr == g->mgr);
    assert(f->mgr == v->mgr);

    result = Cudd_bddCompose(f->mgr,f->node,g->node,(int)Cudd_Regular(v->node)->index);
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_compose */


/**Function********************************************************************

  Synopsis    [Universal Abstraction of Variables.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_consensus(f, quantifying_vars)
bdd_t *f;
array_t *quantifying_vars;	/* of bdd_t *'s */
{
    int i;
    bdd_t *variable;
    DdNode *cube,*tmpDd,*result;
    bdd_manager *mgr;

    /* The Boulder package needs the smothing variables passed as a cube.
    ** Therefore we must build that cube from the indices of the variables
    ** in the array before calling the procedure.
    */
    mgr = f->mgr;
    Cudd_Ref(cube = DD_ONE(mgr));
    for (i = 0; i < array_n(quantifying_vars); i++) {
	variable = array_fetch(bdd_t *,quantifying_vars,i);

	/* Make sure the variable belongs to the same manager */
	assert(mgr == variable->mgr);

        tmpDd = Cudd_bddAnd(mgr,cube,variable->node);
	if (tmpDd == NULL) {
	    Cudd_RecursiveDeref(mgr, cube);
	    return(NULL);
	}
        cuddRef(tmpDd);
	Cudd_RecursiveDeref(mgr, cube);
	cube = tmpDd;
    }

    /* Perform the consensus */
    result = Cudd_bddUnivAbstract(mgr,f->node,cube);
    if (result == NULL) {
	Cudd_RecursiveDeref(mgr, cube);
	return(NULL);
    }
    cuddRef(result);
    /* Get rid of temporary results */
    Cudd_RecursiveDeref(mgr, cube);

    /* Build the bdd_t structure for the result */
    return(bdd_construct_bdd_t(mgr,result));

} /* end of bdd_consensus */


/**Function********************************************************************

  Synopsis    [The compatible projection function.]

  Description [The compatible projection function. The reference minterm
  is chosen based on the phases of the quantifying variables. If all
  variables are in positive phase, the minterm 111...111 is used as
  reference.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_cproject(f, quantifying_vars)
bdd_t *f;
array_t *quantifying_vars;	/* of bdd_t* */
{
    DdManager *dd;
    DdNode *cube;
    DdNode *res;
    bdd_t *fi;
    int nvars, i;

    if (f == NULL) {
	fail ("bdd_cproject: invalid BDD");
    }

    nvars = array_n(quantifying_vars);
    if (nvars <= 0) {
	fail("bdd_cproject: no projection variables");
    }
    dd = f->mgr;

    cube = DD_ONE(dd);
    cuddRef(cube);
    for (i = nvars - 1; i >= 0; i--) {
	DdNode *tmpp;
	fi = array_fetch(bdd_t *, quantifying_vars, i);
	tmpp = Cudd_bddAnd(dd,fi->node,cube);
	if (tmpp == NULL) {
	    Cudd_RecursiveDeref(dd,cube);
	    return(NULL);
	}
	cuddRef(tmpp);
	Cudd_RecursiveDeref(dd,cube);
	cube = tmpp;
    }

    res = Cudd_CProjection(dd,f->node,cube);
    if (res == NULL) {
	Cudd_RecursiveDeref(dd,cube);
	return(NULL);
    }
    cuddRef(res);
    Cudd_RecursiveDeref(dd,cube);

    return(bdd_construct_bdd_t(dd,res));

} /* end of bdd_cproject */


/**Function********************************************************************

  Synopsis    [ITE.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_ite(i, t, e, i_phase, t_phase, e_phase)
bdd_t *i;
bdd_t *t;
bdd_t *e;
boolean i_phase;
boolean t_phase;
boolean e_phase;
{
    DdNode *newi,*newt,*newe,*ite;

    /* Make sure both bdds belong to the same mngr */
    assert(i->mgr == t->mgr);
    assert(i->mgr == e->mgr);

    /* Modify the phases of the operands according to the parameters */
    if (!i_phase) {
	newi = Cudd_Not(i->node);
    } else {
	newi = i->node;
    }
    if (!t_phase) {
	newt = Cudd_Not(t->node);
    } else {
	newt = t->node;
    }
    if (!e_phase) {
	newe = Cudd_Not(e->node);
    } else {
	newe = e->node;
    }

    /* Perform the ITE operation */
    ite = Cudd_bddIte(i->mgr,newi,newt,newe);
    if (ite == NULL) return(NULL);
    cuddRef(ite);
    return(bdd_construct_bdd_t(i->mgr,ite));

} /* end of bdd_ite */


/**Function********************************************************************

  Synopsis    [Restric operator as described in Coudert et al. ICCAD90.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_minimize(f, c)
bdd_t *f;
bdd_t *c;
{
    DdNode *result;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == c->mgr);

    result = Cudd_bddRestrict(f->mgr,f->node,c->node);
    if (result == NULL) return(NULL);
    cuddRef(result);

    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_minimize */


/**Function********************************************************************

  Synopsis    [Parametrized version of the Restrict operator.]

  Description [Parametrized version of the Restrict operator. Currently
  defaults to bdd_minimize.]

  SideEffects []

******************************************************************************/
/*ARGSUSED*/
bdd_t *
bdd_minimize_with_params(f, c, match_type, compl, no_new_vars, return_min)
bdd_t *f;
bdd_t *c;
bdd_min_match_type_t match_type;
boolean compl;
boolean no_new_vars;
boolean return_min;
{
    return(bdd_minimize(f,c));

} /* end of bdd_minimize_with_params */


/**Function********************************************************************

  Synopsis    [Negation.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_not(f)
bdd_t *f;
{
    DdNode *result;

    Cudd_Ref(result = Cudd_Not(f->node));
    return(bdd_construct_bdd_t((DdManager *)f->mgr,result));

} /* end of bdd_not */


/**Function********************************************************************

  Synopsis    [Returns the one BDD.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_one(mgr)
bdd_manager *mgr;
{
    DdNode *result;

    Cudd_Ref(result = DD_ONE((DdManager *)mgr));
    return(bdd_construct_bdd_t((DdManager *)mgr,result));

} /* end of bdd_one */


/**Function********************************************************************

  Synopsis    [Or of two BDDs.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_or(f, g, f_phase, g_phase)
bdd_t *f;
bdd_t *g;
boolean f_phase;
boolean g_phase;
{
    DdNode *newf,*newg,*forg;
    bdd_t *result;

    /* Make sure both bdds belong to the same mngr */
    assert(f->mgr == g->mgr);

    /* Modify the phases of the operands according to the parameters */
    if (f_phase) {
	newf = Cudd_Not(f->node);
    } else {
	newf = f->node;
    }
    if (g_phase) {
	newg = Cudd_Not(g->node);
    } else {
	newg = g->node;
    }

    /* Perform the OR operation */
    forg = Cudd_bddAnd(f->mgr,newf,newg);
    if (forg == NULL) return(NULL);
    forg = Cudd_Not(forg);
    cuddRef(forg);
    result = bdd_construct_bdd_t(f->mgr,forg);

    return(result);

} /* end of bdd_or */


/**Function********************************************************************

  Synopsis    [Existential abstraction of variables.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_smooth(f, smoothing_vars)
bdd_t *f;
array_t *smoothing_vars;	/* of bdd_t *'s */
{
    int i;
    bdd_t *variable;
    DdNode *cube,*tmpDd,*result;
    bdd_manager *mgr;

    /* The Boulder package needs the smothing variables passed as a cube.
    ** Therefore we must build that cube from the indices of the variables
    ** in the array before calling the procedure.
    */
    mgr = f->mgr;
    Cudd_Ref(cube = DD_ONE(mgr));
    for (i = 0; i < array_n(smoothing_vars); i++) {
	variable = array_fetch(bdd_t *,smoothing_vars,i);

	/* Make sure the variable belongs to the same manager. */
	assert(mgr == variable->mgr);

        tmpDd = Cudd_bddAnd(mgr,cube,variable->node);
	if (tmpDd == NULL) {
	    Cudd_RecursiveDeref(mgr, cube);
	    return(NULL);
	}
        cuddRef(tmpDd);
	Cudd_RecursiveDeref(mgr, cube);
	cube = tmpDd;
    }

    /* Perform the smoothing */
    result = Cudd_bddExistAbstract(mgr,f->node,cube);
    if (result == NULL) {
	Cudd_RecursiveDeref(mgr, cube);
	return(NULL);
    }
    cuddRef(result);

    /* Get rid of temporary results */
    Cudd_RecursiveDeref(mgr, cube);

    /* Build the bdd_t structure for the result */
    return(bdd_construct_bdd_t(mgr,result));

} /* end of bdd_smooth */


/**Function********************************************************************

  Synopsis    [Permutes the variables.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_substitute(f, old_array, new_array)
bdd_t *f;
array_t *old_array;	/* of bdd_t *'s */
array_t *new_array;	/* of bdd_t *'s */
{
    int maxOld;
    int i,varIndex,from,to;
    int *permut;
    bdd_t *variable;
    DdNode *result;

    /* Make sure both arrays have the same number of elements. */
    assert(array_n(old_array) == array_n(new_array));

    /* Detect what is the highest index of variable to rename. */
    maxOld = 0;
    for (i = 0; i < array_n(old_array); i++) {
	variable = array_fetch(bdd_t *, old_array, i);
	/* Make sure the variable belongs to this manager. */
	assert(f->mgr == variable->mgr);

	varIndex = Cudd_Regular(variable->node)->index;
	if (varIndex > maxOld) {
	    maxOld = varIndex;
	}
    }
    maxOld++;

    /* Allocate and fill the array with the trivial permutation. */
    permut = ALLOC(int, maxOld);
    for (i = 0; i < maxOld; i++) permut[i] = i;

    /* Modify the permutation by looking at both arrays old and new. */
    for (i = 0; i < array_n(old_array); i++) {
	variable = array_fetch(bdd_t *, old_array, i);
	from = Cudd_Regular(variable->node)->index;
	variable = array_fetch(bdd_t *, new_array, i);
	/* Make sure the variable belongs to this manager. */
	assert(f->mgr == variable->mgr);

	to = Cudd_Regular(variable->node)->index;
	permut[from] = to;
    }

    result = Cudd_bddPermute(f->mgr,f->node,permut);
    FREE(permut);
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_substitute */


/**Function********************************************************************

  Synopsis    [Returns the Then branch of the BDD.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_then(f)
bdd_t *f;
{
    DdNode *result;

    result = Cudd_T(f->node);
    result =  Cudd_NotCond(result,Cudd_IsComplement(f->node));
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_then */


/**Function********************************************************************

  Synopsis    [Returns the else branch of a BDD.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_else(f)
bdd_t *f;
{
    DdNode *result;

    result = Cudd_E(f->node);
    result =  Cudd_NotCond(result,Cudd_IsComplement(f->node));
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_else */


/**Function********************************************************************

  Synopsis    [Returns the BDD of the top variable.]

  Description [Returns the BDD of the top variable of the argument. If
  the argument is constant, it returns the constant function itself.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_top_var(f)
bdd_t *f;
{
    DdNode *result;

    if (Cudd_IsConstant(f->node)) {
	result = f->node;
    } else {
	result = f->mgr->vars[Cudd_Regular(f->node)->index];
    }
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_top_var */


/**Function********************************************************************

  Synopsis    [Computes the exclusive nor of two BDDs.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_xnor(f, g)
bdd_t *f;
bdd_t *g;
{
    DdNode *result;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == g->mgr);

    result = Cudd_bddIte(f->mgr,f->node,g->node,Cudd_Not(g->node));
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_xnor */


/**Function********************************************************************

  Synopsis    [Computes the exclusive or of two BDDs.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_xor(f, g)
bdd_t *f;
bdd_t *g;
{
    DdNode *result;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == g->mgr);

    result = Cudd_bddIte(f->mgr,f->node,Cudd_Not(g->node),g->node);
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_xor */


/**Function********************************************************************

  Synopsis    [Returns the constant zero BDD.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_zero(mgr)
bdd_manager *mgr;
{
    DdNode *result;

    Cudd_Ref(result = Cudd_Not(DD_ONE((mgr))));
    return(bdd_construct_bdd_t(mgr,result));

} /* end of bdd_zero */


/**Function********************************************************************

  Synopsis    [Equality check.]

  SideEffects []

******************************************************************************/
boolean
bdd_equal(f, g)
bdd_t *f;
bdd_t *g;
{
    return(f->node == g->node);

} /* end of bdd_equal */


/**Function********************************************************************

  Synopsis    [Returns a BDD included in the intersection of f and g.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_intersects(f, g)
bdd_t *f;
bdd_t *g;
{
    DdNode *result;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == g->mgr);

    result = Cudd_bddIntersect(f->mgr,f->node,g->node);
    if (result == NULL) return(NULL);
    cuddRef(result);
    return(bdd_construct_bdd_t(f->mgr,result));

} /* end of bdd_intersects */


/**Function********************************************************************

  Synopsis    [Checks a BDD for tautology.]

  SideEffects []

******************************************************************************/
boolean
bdd_is_tautology(f, phase)
bdd_t *f;
boolean phase;
{
    if (phase) {
	return(f->node == DD_ONE(f->mgr));
    } else {
	return(f->node == Cudd_Not(DD_ONE(f->mgr)));
    }

} /* end of bdd_is_tautology */


/**Function********************************************************************

  Synopsis    [Tests for containment of f in g.]

  SideEffects []

******************************************************************************/
boolean
bdd_leq(f, g, f_phase, g_phase)
bdd_t *f;
bdd_t *g;
boolean f_phase;
boolean g_phase;
{
    DdNode *newf, *newg;

    /* Make sure both operands belong to the same manager. */
    assert(f->mgr == g->mgr);

    if (f_phase) {
	newf = f->node;
    } else {
	newf = Cudd_Not(f->node);
    }
    if (g_phase) {
	newg = g->node;
    } else {
	newg = Cudd_Not(g->node);
    }

    return(Cudd_bddLeq(f->mgr,newf,newg));

} /* end of bdd_leq */


/**Function********************************************************************

  Synopsis    [Counts the number of minterms in the on set.]

  SideEffects []

******************************************************************************/
double
bdd_count_onset(f, var_array)
bdd_t *f;
array_t *var_array;  	/* of bdd_t *'s */
{
    return(Cudd_CountMinterm(f->mgr,f->node,array_n(var_array)));

} /* end of bdd_count_onset */


/**Function********************************************************************

  Synopsis    [Obtains the manager of the BDD.]

  SideEffects []

******************************************************************************/
bdd_manager *
bdd_get_manager(f)
bdd_t *f;
{
    return(f->mgr);

} /* end of bdd_get_manager */


/**Function********************************************************************

  Synopsis    [Returns the node of the BDD.]

  SideEffects [Sets is_complemented.]

******************************************************************************/
bdd_node *
bdd_get_node(f, is_complemented)
bdd_t *f;
boolean *is_complemented;    /* return */
{
    if (Cudd_IsComplement(f->node)) {
	*is_complemented = TRUE;
	return(Cudd_Regular(f->node));
    }
    *is_complemented = FALSE;
    return(f->node);

} /* end of bdd_get_node */


/**Function********************************************************************

  Synopsis    [Returns the free field of the BDD.]

  SideEffects []

******************************************************************************/
int
bdd_get_free(f)
bdd_t *f;
{
    return (f->free);

} /* end of bdd_get_free */


/**Function********************************************************************

  Synopsis    [Obtains some statistics of the BDD package.]

  SideEffects [Sets stats.]

******************************************************************************/
/*ARGSUSED*/
void
bdd_get_stats(mgr, stats)
bdd_manager *mgr;
bdd_stats *stats;	/* return */
{
    stats->nodes.total = mgr->keys;
    stats->nodes.used = mgr->keys - mgr->dead;
    stats->nodes.unused = mgr->dead;
    stats->cache.itetable.hits = (unsigned int) Cudd_ReadCacheHits(mgr);
    stats->cache.itetable.misses = (unsigned int)
	(Cudd_ReadCacheLookUps(mgr) - Cudd_ReadCacheHits(mgr));
    stats->cache.itetable.collisions = mgr->cachecollisions;
    stats->cache.itetable.inserts = mgr->cacheinserts;
    stats->gc.times = Cudd_ReadGarbageCollections(mgr);
    return;

} /* end of bdd_get_stats */


/**Function********************************************************************

  Synopsis    [Obtains the support of the BDD.]

  SideEffects []

******************************************************************************/
var_set_t *
bdd_get_support(f)
bdd_t *f;
{
    DdNode *support, *scan;
    var_set_t *result;

    support = Cudd_Support(f->mgr,f->node);
    if (support == NULL) return(NULL);
    cuddRef(support);

    result = var_set_new((int) f->mgr->size);
    scan = support;
    while (!cuddIsConstant(scan)) {
	var_set_set_elt(result, scan->index);
	scan = cuddT(scan);
    }
    Cudd_RecursiveDeref(f->mgr,support);

    return(result);

} /* end of bdd_get_support */


/**Function********************************************************************

  Synopsis    [Obtains the array of indices of an array of variables.]

  SideEffects []

******************************************************************************/
array_t *
bdd_get_varids(var_array)
array_t *var_array;
{
    int i;
    int index;
    bdd_t *var;
    array_t *result = array_alloc(int,array_n(var_array));

    for (i = 0; i < array_n(var_array); i++) {
	var = array_fetch(bdd_t *, var_array, i);
	index = Cudd_Regular(var->node)->index;
	(void) array_insert_last(int, result, index);
    }
    return(result);

} /* end of bdd_get_varids */


/**Function********************************************************************

  Synopsis    [Returns the number of variables in the manager.]

  SideEffects []

******************************************************************************/
unsigned int
bdd_num_vars(mgr)
bdd_manager *mgr;
{
    return(mgr->size);

} /* end of bdd_num_vars */


/**Function********************************************************************

  Synopsis    [Prints the BDD.]

  SideEffects []

******************************************************************************/
void
bdd_print(f)
bdd_t *f;
{
    (void) cuddP(f->mgr,f->node);

} /* end of bdd_print */


/**Function********************************************************************

  Synopsis    [Prints statistics about the package.]

  SideEffects []

******************************************************************************/
void
bdd_print_stats(stats, file)
bdd_stats stats;
FILE *file;
{
#ifndef DD_STATS
    fprintf(stderr,"CU DD package: bdd_print_stats: Statistics turned off. No output\n");
#else
    fprintf(file,"CU DD Package Statistics\n");
    fprintf(file,"  Cache hits : %d\n",stats.cache.itetable.hits);
    fprintf(file,"  Cache misses : %d\n",stats.cache.itetable.misses);
    fprintf(file,"  Cache collisions : %d\n",stats.cache.itetable.collisions);
    fprintf(file,"  Cache inserts: %d\n",stats.cache.itetable.inserts);
#endif
    return;

} /* end of bdd_print_stats */


/**Function********************************************************************

  Synopsis    [Computes the number of nodes of a BDD.]

  SideEffects []

******************************************************************************/
int
bdd_size(f)
bdd_t *f;
{
    return(Cudd_DagSize(f->node));

} /* end of bdd_size */


/**Function********************************************************************

  Synopsis    [Accesses the id of the top variable.]

  SideEffects []

******************************************************************************/
bdd_variableId
bdd_top_var_id(f)
bdd_t *f;
{
    return(Cudd_Regular(f->node)->index);

} /* end of bdd_top_var_id */


/**Function********************************************************************

  Synopsis    [Accesses the external_hooks field of the manager.]

  SideEffects []

******************************************************************************/
bdd_external_hooks *
bdd_get_external_hooks(mgr)
bdd_manager *mgr;
{
    return((bdd_external_hooks *)(mgr->hooks));

} /* end of bdd_get_external_hooks */


/**Function********************************************************************

  Synopsis    [Registers a new hook with the manager.]

  SideEffects []

******************************************************************************/
/*ARGSUSED*/
void
bdd_register_daemon(mgr, daemon)
bdd_manager *mgr;
void (*daemon)();
{
    fprintf(stderr,"CU DD Package: bdd_register_daemon translated to no-op.\n");
    return;

} /* end of bdd_register_daemon */


/**Function********************************************************************

  Synopsis    [Turns on or off garbage collection.]

  SideEffects []

******************************************************************************/
void
bdd_set_gc_mode(mgr, no_gc)
bdd_manager *mgr;
boolean no_gc;
{
    if (no_gc) {
	Cudd_DisableGarbageCollection(mgr);
    } else {
	Cudd_EnableGarbageCollection(mgr);
    }
    return;

} /* end of bdd_set_gc_mode */


/**Function********************************************************************

  Synopsis    [Reorders the BDD pool.]

  SideEffects []

******************************************************************************/
void
bdd_dynamic_reordering(mgr, algorithm_type)
bdd_manager *mgr;
bdd_reorder_type_t algorithm_type;
{
    switch (algorithm_type) {
      case BDD_REORDER_SIFT:
	mgr->autoMethod = CUDD_REORDER_SIFT;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW:
      case BDD_REORDER_WINDOW4:
	mgr->autoMethod = CUDD_REORDER_WINDOW4;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_NONE:
	mgr->autoDyn = 0;
	break;
      case BDD_REORDER_SAME:
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_RANDOM:
	mgr->autoMethod = CUDD_REORDER_RANDOM;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_RANDOM_PIVOT:
	mgr->autoMethod = CUDD_REORDER_RANDOM_PIVOT;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_SIFT_CONVERGE:
	mgr->autoMethod = CUDD_REORDER_SIFT_CONVERGE;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_SYMM_SIFT:
	mgr->autoMethod = CUDD_REORDER_SYMM_SIFT;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_SYMM_SIFT_CONV:
	mgr->autoMethod = CUDD_REORDER_SYMM_SIFT_CONV;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW2:
	mgr->autoMethod = CUDD_REORDER_WINDOW2;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW3:
	mgr->autoMethod = CUDD_REORDER_WINDOW3;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW2_CONV:
	mgr->autoMethod = CUDD_REORDER_WINDOW2_CONV;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW3_CONV:
	mgr->autoMethod = CUDD_REORDER_WINDOW3_CONV;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_WINDOW4_CONV:
	mgr->autoMethod = CUDD_REORDER_WINDOW4_CONV;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_GROUP_SIFT:
	mgr->autoMethod = CUDD_REORDER_GROUP_SIFT;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_GROUP_SIFT_CONV:
	mgr->autoMethod = CUDD_REORDER_GROUP_SIFT_CONV;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_ANNEALING:
	mgr->autoMethod = CUDD_REORDER_ANNEALING;
	mgr->autoDyn = 1;
	break;
      case BDD_REORDER_GENETIC:
	mgr->autoMethod = CUDD_REORDER_GENETIC;
	mgr->autoDyn = 1;
	break;
      default:
	fprintf(stderr,"CU DD Package: Reordering algorithm not considered\n");
    }

} /* end of bdd_dynamic_reordering */


/**Function********************************************************************

  Synopsis    [Calls reordering explicitly.]

  SideEffects []

******************************************************************************/
void
bdd_reorder(mgr)
bdd_manager *mgr;
{
    (void) Cudd_ReduceHeap(mgr,mgr->autoMethod,10); /* 10 = whatever (Verbatim from file ddTable.c) */
    return;

} /* end of bdd_reorder */


/**Function********************************************************************

  Synopsis    [Read the number of reorderings the package has performed
  so far.]

  SideEffects []

******************************************************************************/
int
bdd_read_reorderings(mgr)
bdd_manager *mgr;
{
    return Cudd_ReadReorderings((DdManager *)mgr);

} /* end of bdd_read_reorderings */


/**Function********************************************************************

  Synopsis    [Gets the id variable for one level in the BDD.]

  SideEffects []

******************************************************************************/
bdd_variableId
bdd_get_id_from_level(mgr, level)
bdd_manager *mgr;
long level;
{
    return(mgr->invperm[level]);

} /* end of bdd_get_id_from_level */


/**Function********************************************************************

  Synopsis    [Gets the level of the top variable of the BDD.]

  SideEffects []

******************************************************************************/
long
bdd_top_var_level(mgr, fn)
bdd_manager *mgr;
bdd_t *fn;
{
    return((long) cuddI(mgr,Cudd_Regular(fn->node)->index));

} /* end of bdd_top_var_level */


/**Function********************************************************************

  Synopsis    [Returns TRUE if the argument BDD is a cube; FALSE
  otherwise.]

  SideEffects []

******************************************************************************/
boolean
bdd_is_cube(f)
bdd_t *f;
{
    struct DdManager *manager;

    if (f == NULL) {
	fail("bdd_is_cube: invalid BDD");
    }
    if (f->free) fail ("Freed BDD passed to bdd_is_cube");
    manager = (DdManager *) f->mgr;
    return((boolean)cuddCheckCube(manager,f->node));

} /* end of bdd_is_cube */


/**Function********************************************************************

  Synopsis    [Calls the garbage collector explicitly.]

  SideEffects []

******************************************************************************/
void
bdd_gc(mgr)
bdd_manager *mgr;
{
    cuddGarbageCollect(mgr,1);

} /* end of bdd_gc */


/**Function********************************************************************

  Synopsis    [Computes the shared size of an array of BDDs.]

  Description [Computes the shared size of an array of BDDs. Returns
  CUDD_OUT_OF_MEM in case of failure.]

  SideEffects []

******************************************************************************/
long
bdd_size_multiple(bddArray)
array_t *bddArray;
{
    DdNode **nodeArray;
    bdd_t *bddUnit;
    long result;
    int i;

    nodeArray = ALLOC(DdNode *, array_n(bddArray));
    if (nodeArray == NULL) return(CUDD_OUT_OF_MEM);
    for (i = 0; i < array_n(bddArray); i++) {
	bddUnit = array_fetch(bdd_t *, bddArray, i);
	nodeArray[i] = bddUnit->node;
    }

    result = Cudd_SharingSize(nodeArray,array_n(bddArray));

    /* Clean up */
    FREE(nodeArray);

    return(result);

} /* end of bdd_size_multiple */


/**Function********************************************************************

  Synopsis    [Returns the first cube of the function.
  A generator is also returned, which will iterate over the rest.]

  Description [Defines an iterator on the onset of a BDD.  Two routines
  are provided: bdd_first_cube, which extracts one cube from a BDD and
  returns a bdd_gen structure containing the information necessary to
  continue the enumeration; and bdd_next_cube, which returns 1 if
  another cube was found, and 0 otherwise. A cube is represented as an
  array of bdd_literal (which are integers in {0, 1, 2}), where 0
  represents negated literal, 1 for literal, and 2 for don't care.
  Returns a disjoint cover.  A third routine is there to clean up.]

  SideEffects []

  SeeAlso [bdd_next_cube bdd_gen_free]

******************************************************************************/
bdd_gen *
bdd_first_cube(fn, cube)
bdd_t *fn;
array_t **cube;	/* of bdd_literal */
{
    bdd_manager *manager;
    bdd_gen *gen;
    int i;
    int *icube;
    CUDD_VALUE_TYPE value;

    /* Make sure we receive a valid bdd_t. (So to speak.) */
    assert(fn != 0);

    manager = fn->mgr;

    /* Initialize the generator. */
    gen = ALLOC(bdd_gen,1);
    if (gen == NULL) return(NULL);
    gen->manager = manager;

    gen->cube = array_alloc(bdd_literal, manager->size);
    if (gen->cube == NULL) {
	fail("Bdd Package: Out of memory in bdd_first_cube");
    }

    gen->ddGen = Cudd_FirstCube(manager,fn->node,&icube,&value);
    if (gen->ddGen == NULL) {
	fail("Cudd Package: Out of memory in bdd_first_cube");
    }

    if (!Cudd_IsGenEmpty(gen->ddGen)) {
	/* Copy icube to the array_t cube. */
	for (i = 0; i < manager->size; i++) {
	    int myconst = icube[i];
	    array_insert(bdd_literal, gen->cube, i, myconst);
	}
	*cube = gen->cube;
    }

    return(gen);

} /* end of bdd_first_cube */


/**Function********************************************************************

  Synopsis    [Gets the next cube on the generator. Returns {TRUE,
  FALSE} when {more, no more}.]

  SideEffects []

  SeeAlso     [bdd_first_cube bdd_gen_free]

******************************************************************************/
boolean
bdd_next_cube(gen, cube)
bdd_gen *gen;
array_t **cube;		/* of bdd_literal */
{
    int retval;
    int *icube;
    CUDD_VALUE_TYPE value;
    int i;

    retval = Cudd_NextCube(gen->ddGen,&icube,&value);
    if (!Cudd_IsGenEmpty(gen->ddGen)) {
	/* Copy icube to the array_t cube. */
	for (i = 0; i < gen->manager->size; i++) {
	    int myconst = icube[i];
	    array_insert(bdd_literal, gen->cube, i, myconst);
	}
	*cube = gen->cube;
    }

    return(retval);

} /* end of bdd_next_cube */


/**Function********************************************************************

  Synopsis    [Gets the first node in the BDD and returns a generator.]

  SideEffects []

  SeeAlso [bdd_next_node]

******************************************************************************/
bdd_gen *
bdd_first_node(fn, node)
bdd_t *fn;
bdd_node **node;	/* return */
{
    bdd_manager *manager;
    bdd_gen *gen;

    /* Make sure we receive a valid bdd_t. (So to speak.) */
    assert(fn != 0);

    manager = fn->mgr;

    /* Initialize the generator. */
    gen = ALLOC(bdd_gen,1);
    if (gen == NULL) return(NULL);
    gen->manager = manager;
    gen->cube = NULL;

    gen->ddGen = Cudd_FirstNode(manager,fn->node,node);
    if (gen->ddGen == NULL) {
	fail("Cudd Package: Out of memory in bdd_first_node");
    }

    return(gen);

} /* end of bdd_first_node */


/**Function********************************************************************

  Synopsis    [Gets the next node in the BDD. Returns {TRUE, FALSE} when
  {more, no more}.]

  SideEffects []

  SeeAlso [bdd_first_node]

******************************************************************************/
boolean
bdd_next_node(gen, node)
bdd_gen *gen;
bdd_node **node;	/* return */
{
    return(Cudd_NextNode(gen->ddGen,node));

} /* end of bdd_next_node */


/**Function********************************************************************

  Synopsis    [Frees up the space used by the generator. Returns an int
  so that it is easier to fit in a foreach macro. Returns 0 (to make it
  easy to put in expressions).]

  SideEffects []

  SeeAlso []

******************************************************************************/
int
bdd_gen_free(gen)
bdd_gen *gen;
{
    if (gen->cube != NULL) array_free(gen->cube);
    Cudd_GenFree(gen->ddGen);
    FREE(gen);
    return(0);

} /* end of bdd_gen_free */


/**Function********************************************************************

  Synopsis    [Queries the status of a generator.]

  Description [Queries the status of a generator. Returns 1 if the
  generator is empty or NULL; 0 otherswise.]

  SideEffects []

  SeeAlso [bdd_first_cube bdd_next_cube bdd_first_node bdd_next_node
  bdd_gen_free]

******************************************************************************/
boolean
bdd_is_gen_empty(gen)
bdd_gen *gen;
{
    return(Cudd_IsGenEmpty(gen->ddGen));

} /* end of bdd_is_gen_empty */


/**Function********************************************************************

  Synopsis    [Function that creates a variable of a given index.]

  SideEffects []

******************************************************************************/
bdd_t *
bdd_var_with_index(manager, index)
bdd_manager *manager;
int index;
{
    DdNode *var;

    var = Cudd_bddIthVar(manager, index);
    cuddRef(var);
    return(bdd_construct_bdd_t(manager, var));

} /* end of bdd_var_with_index */


/**Function********************************************************************

  Synopsis    [Temporary function that is empty.]

  SideEffects []

******************************************************************************/
/*ARGSUSED*/
void
bdd_new_var_block(f, n)
bdd_t *f;
long n;
{
    return;

} /* end of bdd_new_var_block */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Builds the bdd_t structure.]

  Description [Builds the bdd_t structure from manager and node.
  Assumes that the reference count of the node has already been
  increased.]

  SideEffects []

******************************************************************************/
static bdd_t *
bdd_construct_bdd_t(mgr,fn)
DdManager *mgr;
DdNode * fn;
{
    bdd_t *result;

    result = ALLOC(bdd_t, 1);
    if (result == NULL) {
	Cudd_RecursiveDeref(mgr,fn);
	return(NULL);
    }
    result->mgr = mgr;
    result->node = fn;
    result->free = FALSE;
    return(result);

} /* end of bdd_construct_bdd_t */
