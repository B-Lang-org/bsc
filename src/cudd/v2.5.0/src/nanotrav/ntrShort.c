/**CFile***********************************************************************

  FileName    [ntrShort.c]

  PackageName [ntr]

  Synopsis    [Symbolic shortest paths algorithms.]

  Description [This file contains the functions that implement the
  symbolic version of several shortest path algorithms described in the
  JFM paper on ADDs.]

  Author      [Fabio Somenzi, Iris Bahar]

  Copyright   [Copyright (c) 1995-2012, Regents of the University of Colorado

  All rights reserved.

  Redistribution and use in source and binary forms, with or without
  modification, are permitted provided that the following conditions
  are met:

  Redistributions of source code must retain the above copyright
  notice, this list of conditions and the following disclaimer.

  Redistributions in binary form must reproduce the above copyright
  notice, this list of conditions and the following disclaimer in the
  documentation and/or other materials provided with the distribution.

  Neither the name of the University of Colorado nor the names of its
  contributors may be used to endorse or promote products derived from
  this software without specific prior written permission.

  THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
  "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
  LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
  FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
  COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
  INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
  BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
  LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
  CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
  LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
  ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
  POSSIBILITY OF SUCH DAMAGE.]

******************************************************************************/

#include "ntr.h"
#include "cuddInt.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

#ifndef lint
static char rcsid[] UTIL_UNUSED = "$Id: ntrShort.c,v 1.5 2012/02/05 01:53:01 fabio Exp fabio $";
#endif

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static DdNode * ntrBellman (DdManager *dd, DdNode *D, DdNode *source, DdNode **x, DdNode **y, int vars, int pr);
static DdNode * ntrWarshall (DdManager *dd, DdNode *D, DdNode **x, DdNode **y, int vars, int pr);
static DdNode * ntrSquare (DdManager *dd, DdNode *D, DdNode **x, DdNode **y, DdNode **z, int vars, int pr, int st);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/

/**Function********************************************************************

  Synopsis    [Computes shortest paths in a state graph.]

  Description [Computes shortest paths in the state transition graph of
  a network.  Three methods are availabe:
  <ul>
  <li> Bellman-Ford algorithm for single-source shortest paths; the
  algorithm computes the distance (number of transitions) from the initial
  states to all states.
  <li> Floyd-Warshall algorithm for all-pair shortest paths.
  <li> Repeated squaring algorithm for all-pair shortest paths.
  </ul>
  The function returns 1 in case of success; 0 otherwise.
  ]

  SideEffects [ADD variables are created in the manager.]

  SeeAlso     []

******************************************************************************/
int
Ntr_ShortestPaths(
  DdManager * dd,
  BnetNetwork * net,
  NtrOptions * option)
{
    NtrPartTR *TR;
    DdNode *edges, *source, *res, *r, *q, *bddSource;
    DdNode **xadd, **yadd, **zadd;
    int i;
    int pr = option->verb;
    int algorithm = option->shortPath;
    int selectiveTrace = option->selectiveTrace;
    int nvars = net->nlatches;

    /* Set background to infinity for shortest paths. */
    Cudd_SetBackground(dd,Cudd_ReadPlusInfinity(dd));

    /* Build the monolithic TR. */
    TR = Ntr_buildTR(dd,net,option,NTR_IMAGE_MONO);

    /* Build the ADD variable vectors for x and y. */
    xadd = ALLOC(DdNode *, nvars);
    yadd = ALLOC(DdNode *, nvars);
    for(i = 0; i < nvars; i++) {
	q = Cudd_addIthVar(dd,TR->x[i]->index);
	Cudd_Ref(q);
	xadd[i] = q;
	q = Cudd_addIthVar(dd,TR->y[i]->index);
	Cudd_Ref(q);
	yadd[i] = q;
    }

    /* Convert the transition relation BDD into an ADD... */
    q = Cudd_BddToAdd(dd,TR->part[0]);
    Cudd_Ref(q);
    /* ...replacing zeroes with infinities... */
    r = Cudd_addIte(dd,q,Cudd_ReadOne(dd),Cudd_ReadPlusInfinity(dd));
    Cudd_Ref(r);
    Cudd_RecursiveDeref(dd,q);
    /* ...and zeroing the diagonal. */
    q = Cudd_addXeqy(dd,nvars,xadd,yadd);
    Cudd_Ref(q);
    edges = Cudd_addIte(dd,q,Cudd_ReadZero(dd),r);
    Cudd_Ref(edges);
    Cudd_RecursiveDeref(dd,r);
    Cudd_RecursiveDeref(dd,q);

    switch(algorithm) {
    case NTR_SHORT_BELLMAN:
	bddSource = Ntr_initState(dd,net,option);
	source = Cudd_BddToAdd(dd,bddSource);
	Cudd_Ref(source);
	res = ntrBellman(dd,edges,source,xadd,yadd,nvars,pr);
	if (res == NULL) return(0);
	Cudd_Ref(res);
	Cudd_RecursiveDeref(dd,source);
	Cudd_RecursiveDeref(dd,bddSource);
	if (pr >= 0) {
	    (void) fprintf(stdout,"Distance Matrix");
	    Cudd_PrintDebug(dd,res,nvars,pr);
	}
	break;
    case NTR_SHORT_FLOYD:
	res = ntrWarshall(dd,edges,xadd,yadd,nvars,pr);
	if (res == NULL) return(0);
	Cudd_Ref(res);
	if (pr >= 0) {
	    (void) fprintf(stdout,"Distance Matrix");
	    Cudd_PrintDebug(dd,res,2*nvars,pr);
	}
	break;
    case NTR_SHORT_SQUARE:
	/* Create a third set of ADD variables. */
	zadd = ALLOC(DdNode *, nvars);
	for(i = 0; i < nvars; i++) {
	    int level;
	    level = Cudd_ReadIndex(dd,TR->x[i]->index);
	    q = Cudd_addNewVarAtLevel(dd,level);
	    Cudd_Ref(q);
	    zadd[i] = q;
	}
	/* Compute the shortest paths. */
	res = ntrSquare(dd,edges,zadd,yadd,xadd,nvars,pr,selectiveTrace);
	if (res == NULL) return(0);
	Cudd_Ref(res);
	/* Dispose of the extra variables. */
	for(i = 0; i < nvars; i++) {
	    Cudd_RecursiveDeref(dd,zadd[i]);
	}
	FREE(zadd);
	if (pr >= 0) {
	    (void) fprintf(stdout,"Distance Matrix");
	    Cudd_PrintDebug(dd,res,2*nvars,pr);
	}
	break;
    default:
	(void) printf("Unrecognized method. Try again.\n");
	return(0);
    }

    /* Here we should compute the paths. */

    /* Clean up. */
    Ntr_freeTR(dd,TR);
    Cudd_RecursiveDeref(dd,edges);
    Cudd_RecursiveDeref(dd,res);
    for(i = 0; i < nvars; i++) {
	Cudd_RecursiveDeref(dd,xadd[i]);
	Cudd_RecursiveDeref(dd,yadd[i]);
    }
    FREE(xadd);
    FREE(yadd);

    if (option->autoDyn & 1) {
	(void) printf("Order after short path computation\n");
	if (!Bnet_PrintOrder(net,dd)) return(0);
    }

    return(1);

} /* end of Ntr_ShortestPaths */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Bellman-Ford algorithm for single-source shortest paths.]

  Description [Bellman-Ford algorithm for single-source shortest
  paths.  Returns the vector of the distances of all states from the
  initial states.  In case of multiple initial states the distance for
  each state is from the nearest initial state.  Negative-weight
  cycles are detected, though only in the naive way.  (Lack of
  convergence after nodes-1 iterations.)  In such a case, a constant
  ADD with value minus infinity is returned.  Bellman-Ford is based on
  matrix-vector multiplication.  The matrix is the distance matrix
  D(x,y), such that D(a,b) is the length of the arc connecting state a
  to state b.  The vector V(x) stores the distances of all states from
  the initial states.  The actual vector used in the matrix-vector
  multiplication is diff(x), that holds those distances that have
  changed during the last update.]

  SideEffects []

  SeeAlso     [ntrWarshall ntrSquare]

******************************************************************************/
static DdNode *
ntrBellman(
  DdManager *dd,
  DdNode *D,
  DdNode *source,
  DdNode **x,
  DdNode **y,
  int vars,
  int pr)
{
    DdNode *u, *w, *V, *min, *diff;
    DdApaNumber i, nodes, one;
    int digits = vars + 1;

    /* To avoid overflow when there are many variables, use APA. */
    nodes = Cudd_NewApaNumber(digits);
    Cudd_ApaPowerOfTwo(digits,nodes,vars);
    i = Cudd_NewApaNumber(digits);
    one = Cudd_NewApaNumber(digits);
    Cudd_ApaSetToLiteral(digits,one,1);

#if 0
    /* Find the distances from the initial state along paths using one
    ** arc. */
    w = Cudd_Cofactor(dd,D,source); /* works only if source is a cube */
    Cudd_Ref(w);
    V = Cudd_addSwapVariables(dd,w,x,y,vars);
    Cudd_Ref(V);
    Cudd_RecursiveDeref(dd,w);
#endif

    /* The initial states are at distance 0. The other states are
    ** initially at infinite distance. */
    V = Cudd_addIte(dd,source,Cudd_ReadZero(dd),Cudd_ReadPlusInfinity(dd));
    Cudd_Ref(V);

    /* Selective trace algorithm.  For the next update, only consider the
    ** nodes whose distance has changed in the last update. */
    diff = V;
    Cudd_Ref(diff);

    for (Cudd_ApaSetToLiteral(digits,i,1);
	 Cudd_ApaCompare(digits,i,digits,nodes) < 0;
	 Cudd_ApaAdd(digits,i,one,i)) {
	if (pr>2) {(void) printf("V"); Cudd_PrintDebug(dd,V,vars,pr);}
	/* Compute the distances via triangulation as a function of x. */
	w = Cudd_addTriangle(dd,diff,D,x,vars);
	Cudd_Ref(w);
	Cudd_RecursiveDeref(dd,diff);
	u = Cudd_addSwapVariables(dd,w,x,y,vars);
	Cudd_Ref(u);
	Cudd_RecursiveDeref(dd,w);
	if (pr>2) {(void) printf("u"); Cudd_PrintDebug(dd,u,vars,pr);}

	/* Take the minimum of the previous distances and those just
	** computed. */
	min = Cudd_addApply(dd,Cudd_addMinimum,V,u);
	Cudd_Ref(min);
	Cudd_RecursiveDeref(dd,u);
	if (pr>2) {(void) printf("min"); Cudd_PrintDebug(dd,min,vars,pr);}

	if (V == min) {		/* convergence */
	    Cudd_RecursiveDeref(dd,min);
	    if (pr>0) {
		(void) printf("Terminating after ");
		Cudd_ApaPrintDecimal(stdout,digits,i);
		(void) printf(" iterations\n");
	    }
	    break;
	}
	/* Find the distances that decreased. */
	diff = Cudd_addApply(dd,Cudd_addDiff,V,min);
	Cudd_Ref(diff);
	if (pr>2) {(void) printf("diff"); Cudd_PrintDebug(dd,diff,vars,pr);}
	Cudd_RecursiveDeref(dd,V);
	V = min;
    }
    /* Negative cycle detection. */
    if (Cudd_ApaCompare(digits,i,digits,nodes) == 0 &&
	diff != Cudd_ReadPlusInfinity(dd)) {
	(void) printf("Negative cycle\n");
	Cudd_RecursiveDeref(dd,diff);
	Cudd_RecursiveDeref(dd,V);
	V = Cudd_ReadMinusInfinity(dd);
	Cudd_Ref(V);
    }

    Cudd_Deref(V);
    FREE(i);
    FREE(nodes);
    FREE(one);
    return(V);

} /* end of ntrBellman */


/**Function********************************************************************

  Synopsis    [Floyd-Warshall algorithm for all-pair shortest paths.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
static DdNode *
ntrWarshall(
  DdManager *dd,
  DdNode *D,
  DdNode **x,
  DdNode **y,
  int vars,
  int pr)
{
    DdNode *one, *zero;
    DdNode *xminterm,  *w, *V, *V2;
    DdNode *P, *R;
    int i;
    int nodes;
    int k,u;
    long start_time;
    if (vars > 30)
	nodes = 1000000000;
    else
	nodes = 1 << vars;

    one = DD_ONE(dd);
    zero = DD_ZERO(dd);
    Cudd_Ref(R = D);                        /* make copy of original matrix */

    /* Extract pivot row and column from D */
    start_time = util_cpu_time();
    for (k = 0; k < nodes; k++) {
        if (k % 10000 == 0) {
	    (void) printf("Starting iteration  %d  at time %s\n",
			  k,util_print_time(util_cpu_time() - start_time));
        }
        Cudd_Ref(xminterm = one);
        u = k;
	for (i = vars-1; i >= 0; i--) {
	    if (u&1) {
	        Cudd_Ref(w = Cudd_addIte(dd,x[i],xminterm,zero));
	    } else {
	        Cudd_Ref(w = Cudd_addIte(dd,x[i],zero,xminterm));
	    }
	    Cudd_RecursiveDeref(dd,xminterm);
	    xminterm = w;
	    u >>= 1;
	}

	Cudd_Ref(V = Cudd_Cofactor(dd,R,xminterm));
	Cudd_RecursiveDeref(dd,xminterm);
	if (pr>2) {(void) printf("V"); Cudd_PrintDebug(dd,V,vars,pr);}


	Cudd_Ref(xminterm = one);
	u = k;
	for (i = vars-1; i >= 0; i--) {
	    if (u&1) {
	        Cudd_Ref(w = Cudd_addIte(dd,y[i],xminterm,zero));
	    } else {
	        Cudd_Ref(w = Cudd_addIte(dd,y[i],zero,xminterm));
	    }
	    Cudd_RecursiveDeref(dd,xminterm);
	    xminterm = w;
	    u >>= 1;
	}

	Cudd_Ref(V2 = Cudd_Cofactor(dd,R,xminterm));
	Cudd_RecursiveDeref(dd,xminterm);
	if (pr>2) {(void) printf("V2"); Cudd_PrintDebug(dd,V2,vars,pr);}

	Cudd_Ref(P = Cudd_addOuterSum(dd,R,V,V2));

	Cudd_RecursiveDeref(dd,V);
	Cudd_RecursiveDeref(dd,V2);
	Cudd_RecursiveDeref(dd,R);
	R = P;
	if (pr>2) {(void) printf("R"); Cudd_PrintDebug(dd,R,vars,pr);}
    }

    Cudd_Deref(R);
    return(R);

} /* end of ntrWarshall */


/**Function********************************************************************

  Synopsis    [Repeated squaring algorithm for all-pairs shortest paths.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
static DdNode *
ntrSquare(
  DdManager *dd /* manager */,
  DdNode *D /* D(z,y): distance matrix */,
  DdNode **x /* array of x variables */,
  DdNode **y /* array of y variables */,
  DdNode **z /* array of z variables */,
  int vars /* number of variables in each of the three arrays */,
  int pr /* verbosity level */,
  int st /* use the selective trace algorithm */)
{
    DdNode *zero;
    DdNode *I;              /* identity matirix */
    DdNode *w, *V, *P, *M, *R, *RT;
    DdNode *diff, *min, *minDiag;
    int n;
    int neg;
    long start_time;

    zero = Cudd_ReadZero(dd);
    /* Make a working copy of the original matrix. */
    R = D;
    Cudd_Ref(R);
    I = Cudd_addXeqy(dd,vars,z,y);    /* identity matrix */
    Cudd_Ref(I);

    /* Make a copy of the matrix for the selective trace algorithm. */
    diff = R;
    Cudd_Ref(diff);

    start_time = util_cpu_time();
    for (n = vars; n >= 0; n--) {
	printf("Starting iteration %d at time %s\n",vars-n,
	       util_print_time(util_cpu_time() - start_time));

	/* Check for negative cycles: They are identified by negative
	** elements on the diagonal.
	*/

	/* Extract values from the diagonal. */
        Cudd_Ref(w = Cudd_addIte(dd,I,R,zero));
	minDiag = Cudd_addFindMin(dd,w);	/* no need to ref */
	neg = Cudd_V(minDiag) < 0;
	Cudd_RecursiveDeref(dd,w);
	if (neg) {
	    Cudd_RecursiveDeref(dd,diff);
            (void) printf("Negative cycle after %d iterations!\n",vars-n);
            break;
        }

	/* Prepare the first operand of matrix multiplication:
	**   diff(z,y) -> RT(x,y) -> V(x,z)
	*/

	/* RT(x,y) */
	Cudd_Ref(RT = Cudd_addSwapVariables(dd,diff,x,z,vars));
	Cudd_RecursiveDeref(dd,diff);
	/* V(x,z) */
	Cudd_Ref(V = Cudd_addSwapVariables(dd,RT,y,z,vars));
	Cudd_RecursiveDeref(dd,RT);
	if (pr > 0) {
	    double pathcount;
	    (void) printf("V"); Cudd_PrintDebug(dd,V,2*vars,pr);
	    pathcount = Cudd_CountPath(V);
	    (void) printf("Path count = %g\n", pathcount);
	}

	/* V(x,z) * R(z,y) -> P(x,y) */
	Cudd_Ref(P = Cudd_addTriangle(dd,V,R,z,vars));
	Cudd_RecursiveDeref(dd,V);
	/* P(x,y) => M(z,y) */
	Cudd_Ref(M = Cudd_addSwapVariables(dd,P,x,z,vars));
	Cudd_RecursiveDeref(dd,P);
	if (pr>0) {(void) printf("M"); Cudd_PrintDebug(dd,M,2*vars,pr);}

	/* min(z,y) */
	Cudd_Ref(min = Cudd_addApply(dd,Cudd_addMinimum,R,M));
	Cudd_RecursiveDeref(dd,M);

	if (R == min) {
	    Cudd_RecursiveDeref(dd,min);
	    if (pr>0) {printf("Done after %d iterations\n",vars-n+1); }
	    break;
	}
	/* diff(z,y) */
	if (st) {
	    Cudd_Ref(diff = Cudd_addApply(dd,Cudd_addDiff,min,R));
	} else {
	    Cudd_Ref(diff = min);
	}
	Cudd_RecursiveDeref(dd,R);
	R = min;                  /* keep a copy of matrix at current iter. */
	if (pr > 0) {
	    double pathcount;
	    (void) printf("R"); Cudd_PrintDebug(dd,R,2*vars,pr);
	    pathcount = Cudd_CountPath(R);
	    (void) printf("Path count = %g\n", pathcount);
	}

	if (n == 0) {
	    (void) printf("Negative cycle!\n");
	    break;
	}

    }
    Cudd_RecursiveDeref(dd,I);
    Cudd_Deref(R);
    return(R);

} /* end of ntrSquare */
