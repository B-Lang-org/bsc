/**CFile***********************************************************************

  FileName    [ntrMflow.c]

  PackageName [ntr]

  Synopsis    [Symbolic maxflow algorithm.]

  Description [This file contains the functions that implement the
  symbolic version of Dinits's maxflow algorithm described in the
  ICCAD93 paper. The present implementation differs from the algorithm
  described in the paper in that more than one matching techniques is
  used. The technique of the paper is the one applied to
  hourglass-type bilayers here.]

  Author      [Fabio Somenzi, Gary Hachtel]

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

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define MAXPHASE 1000
#define MAXLAYER 1000
#define MAXFPIT  100000
#define MANY_TIMES 3.0

#define PRUNE		/* If defined, enables pruning of E */

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

typedef struct flowStatsStruct {
    int pr;			/* level of verbosity */
    long start_time;		/* cpu time when the covering started */
    int phases;			/* number of phases */
    int layers;			/* number of layers */
    int fpit;			/* number of fixed point iterations */
} flowStats;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

#ifndef lint
static char rcsid[] UTIL_UNUSED = "$Id: ntrMflow.c,v 1.8 2012/02/05 01:53:01 fabio Exp fabio $";
#endif

static DdNode *xcube, *ycube, *zcube;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void maximal_pull (DdManager *bdd, int l, DdNode *ty, DdNode **neW, DdNode **U, DdNode *E, DdNode **F, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void propagate_maximal_flow (DdManager *bdd, int m, DdNode **neW, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void trellis (DdManager *bdd, int m, DdNode **neW, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void rhombus (DdManager *bdd, int m, DdNode **neW, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void hourglass (DdManager *bdd, int m, DdNode **neW, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void maximal_push (DdManager *bdd, int l, DdNode **U, DdNode **F, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void trellisPush (DdManager *bdd, int m, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void rhombusPush (DdManager *bdd, int m, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);
static void hourglassPush (DdManager *bdd, int m, DdNode **U, DdNode **x, DdNode **y, DdNode **z, int n, DdNode *pryz, DdNode *prxz, flowStats *stats);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    []

  Description [This function implements Dinits's algorithm for (0-1)
  max flow, using BDDs and a symbolic technique to trace multiple
  edge-disjoint augmenting paths to complete a phase. The outer
  forever loop is over phases, and the inner forever loop is to
  propagate a (not yet) maximal flow of edge-disjoint augmenting paths
  from one layer to the previous. The subprocedure call implements a
  least fixed point iteration to compute a (not yet) maximal flow
  update between layers. At the end of each phase (except the last
  one) the flow is actually pushed from the source to the sink.

  Data items:
    <ul>
    <li> sx(ty)	BDD representations of s(t).
    <li> x(y)	The variables encoding the from(to)-node u(v) of an
		edge (u,v) in the given digraph.
    <li> z	Another set of variables.
    <li> E(x,y)	The edge relation.
    <li> F(x,y) BDD representation of the current flow, initialized to 0
		for each arc, and updated by +1, -1, or 0 at the
		end of each phase.
    <li> Ms Mt	The maximum flow, that is, the cardinality of a minimum cut,
		measured at the source and at the sink, respectively.
		The two values should be identical.
    <li> reached The set of nodes already visited in the BFS of the digraph.
    <li> fos	fanout of the source node s.
    <li> fit	fanin of the sink node t.
    </ul>
  ]

  SideEffects [The flow realtion F and the cutset relation cut are returned
  as side effects.]

  SeeAlso     []

******************************************************************************/
double
Ntr_maximum01Flow(
  DdManager * bdd /* manager */,
  DdNode * sx /* source node */,
  DdNode * ty /* sink node */,
  DdNode * E /* edge relation */,
  DdNode ** F /* flow relation */,
  DdNode ** cut /* cutset relation */,
  DdNode ** x /* array of row variables */,
  DdNode ** y /* array of column variables */,
  DdNode ** z /* arrays of auxiliary variables */,
  int  n /* number of variables in each array */,
  int  pr /* verbosity level */)
{
    flowStats stats;
    DdNode *one, *zero,
#ifdef PRUNE
	     *EDC,	    /* Edge don't care set */
#endif
	     *reached,      /* states reached through useful edges */
	     *fos, *fit,    /* fanout of source, fanin of sink */
	     *rF, *rB, *tx,
	     *I, *P,
	     *w, *p, *q, *r,/* intemediate results */
	     *pryz, *prxz,  /* priority functions for disjoint path tracing */
	     **neW, **U;    /* arrays of BDDs for flow propagation */
    int	     i, j, l;
    double   Ms, Mt;

    /* Initialize debugging structure. */
    stats.pr = pr;
    stats.start_time = util_cpu_time();
    stats.phases = 0;
    stats.layers = 0;
    stats.fpit = 0;

    /* Allocate arrays for new (just reached vertex sets)
    ** and U (useful edge sets).
    */
    U   = ALLOC(DdNode *, ((unsigned) MAXLAYER));
    neW = ALLOC(DdNode *, ((unsigned) MAXLAYER));

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /* Initialize xcube, ycube, and zcube (for abstractions). */
    Cudd_Ref(xcube = Cudd_bddComputeCube(bdd,x,NULL,n));
    Cudd_Ref(ycube = Cudd_bddComputeCube(bdd,y,NULL,n));
    Cudd_Ref(zcube = Cudd_bddComputeCube(bdd,z,NULL,n));

    /* Build the BDD for the priority functions. */
    Cudd_Ref(pryz = Cudd_Dxygtdxz(bdd, n, x, y, z));
    Cudd_Ref(prxz = Cudd_Dxygtdyz(bdd, n, x, y, z));
    /* Now "randomize" by shuffling the x variables in pryz and the y
    ** variables in prxz.
    */
    Cudd_Ref(p = Cudd_bddAdjPermuteX(bdd,pryz,x,n));
    Cudd_RecursiveDeref(bdd,pryz);
    pryz = p;
    if(pr>2){(void) fprintf(stdout,"pryz");Cudd_PrintDebug(bdd,pryz,n*3,pr);}
    Cudd_Ref(p = Cudd_bddAdjPermuteX(bdd,prxz,y,n));
    Cudd_RecursiveDeref(bdd,prxz);
    prxz = p;
    if(pr>2){(void) fprintf(stdout,"prxz");Cudd_PrintDebug(bdd,prxz,n*3,pr);}

#ifdef PRUNE
    /* Build the edge don't care set and prune E. The edge don't care
    ** set consists of the edges into the source(s), the edges out of the
    ** sink(s), and the self-loops. These edges cannot contribute to the
    ** maximum flow.
    */
    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, sx, x, y, n));
    Cudd_Ref(q = Cudd_bddSwapVariables(bdd, ty, x, y, n));
    Cudd_Ref(r = Cudd_bddOr(bdd, p, q));
    Cudd_RecursiveDeref(bdd,p);
    Cudd_RecursiveDeref(bdd,q);
    Cudd_Ref(p = Cudd_Xeqy(bdd, n, x, y));
    Cudd_Ref(EDC = Cudd_bddOr(bdd, p, r));
    Cudd_RecursiveDeref(bdd,p);
    Cudd_RecursiveDeref(bdd,r);
    if(pr>2){(void) fprintf(stdout,"EDC");Cudd_PrintDebug(bdd,EDC,n<<1,pr);}
    Cudd_Ref(p = Cudd_bddAnd(bdd, E, Cudd_Not(EDC)));
    Cudd_RecursiveDeref(bdd,EDC);
    if(pr>0){(void) fprintf(stdout,"Given  E");Cudd_PrintDebug(bdd,E,n<<1,pr);}
    E = p;
    if(pr>0){(void) fprintf(stdout,"Pruned E");Cudd_PrintDebug(bdd,E,n<<1,pr);}
#endif

    /* Compute fanin of sink node t: it is an upper bound for the flow. */
    Cudd_Ref(fit = Cudd_bddAnd(bdd, E, ty));
    if (pr>2) {
	/* Compute fanout of source node s. */
	Cudd_Ref(fos = Cudd_bddAnd(bdd, E, sx));
	(void) fprintf(stdout,"fos");Cudd_PrintDebug(bdd,fos,n<<1,pr);
	Cudd_RecursiveDeref(bdd,fos);

	(void) fprintf(stdout,"fit");Cudd_PrintDebug(bdd,fit,n<<1,pr);
    }
    /* t(x) is used to check for termination of forward traversal. */
    Cudd_Ref(tx = Cudd_bddSwapVariables(bdd, ty, x, y, n));

    /* \KW{Procedure}\ \ \PC{maximum\_flow}$(s,t,E(x,y)) */
    Cudd_Ref(*F = zero);

    for (i = 1; i < MAXPHASE; i++) {
	stats.phases++;
	if(pr>0){(void) fprintf(stdout,"## Starting Phase %d at time = %s\n",i,
		util_print_time(util_cpu_time() - stats.start_time));}
	/* new[0](x) = s(x);U^0(x,y)=E(x,y)\cdot s(x) \cdot \overline{F(x,y)};
	** reached=s; new[1](x)=\exists_xU^0(x,y);
	*/
	Cudd_Ref(neW[0] = sx);
	Cudd_Ref(p = Cudd_bddAnd(bdd, sx, Cudd_Not(*F)));
	Cudd_Ref(U[0] = Cudd_bddAnd(bdd, p, E));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(reached = sx);
	Cudd_Ref(r = Cudd_bddExistAbstract(bdd, U[0], xcube));
	Cudd_RecursiveDeref(bdd,U[0]);
	Cudd_Ref(q = Cudd_bddSwapVariables(bdd, r, x, y, n));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_Ref(neW[1] = Cudd_bddAnd(bdd, q, Cudd_Not(reached)));
	Cudd_RecursiveDeref(bdd,q);
	if(pr>0) {
	    (void) fprintf(stdout,"neW[1]");Cudd_PrintDebug(bdd,neW[1],n,pr);
	}
	for (l = 1; l < MAXLAYER; l++) {
	    if (neW[l] == zero) {	/* flow is maximum */
		/* cut=reached(x) \cdot E(x,y) \cdot \overline{reached(y)} */
		Cudd_Ref(p = Cudd_bddAnd(bdd, reached, E));
		Cudd_Ref(q = Cudd_bddSwapVariables(bdd, reached, x, y, n));
		Cudd_Ref(*cut = Cudd_bddAnd(bdd, p, Cudd_Not(q)));
		Cudd_RecursiveDeref(bdd,p);
		Cudd_RecursiveDeref(bdd,q);
		Cudd_RecursiveDeref(bdd,reached);
		for (j = 0; j <= l; j++)
		    Cudd_RecursiveDeref(bdd,neW[j]);
		goto endPhases;
	    }
	    /* As soon as we touch one sink node we stop traversal.
	    ** \KW{if} ($t\cdot new^{l} \neq 0$)
	    */
	    if (!Cudd_bddLeq(bdd, tx, Cudd_Not(neW[l]))) {
		Cudd_RecursiveDeref(bdd,reached);
		maximal_pull(bdd,l-1,ty,neW,U,E,F,x,y,z,n,pryz,prxz,&stats);
		goto endLayers;
	    }
	    stats.layers++;
	    if(pr>2){(void) fprintf(stdout,"===== Layer %d =====\n",l);}
	    /* reached(x) = reached(x) + new^l(x) */
	    Cudd_Ref(w = Cudd_bddOr(bdd, reached, neW[l]));
	    Cudd_RecursiveDeref(bdd,reached);
	    reached = w;
	    /* I(y) = \exists_x((E(x,y) \cdot \overline{F(x,y)})
	    **        \cdot new^l(x))
	    */
	    Cudd_Ref(p = Cudd_bddAnd(bdd, E, Cudd_Not(*F)));
	    Cudd_Ref(I = Cudd_bddAndAbstract(bdd, p, neW[l], xcube));
	    if(pr>3){(void) fprintf(stdout,"I");Cudd_PrintDebug(bdd,I,n,pr);}
	    Cudd_RecursiveDeref(bdd,p);
	    /* rF(x)= I(x) \cdot \overline{reached(x)}) */
	    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, I, x, y, n));
	    Cudd_RecursiveDeref(bdd,I);
	    Cudd_Ref(rF = Cudd_bddAnd(bdd, p, Cudd_Not(reached)));
	    Cudd_RecursiveDeref(bdd,p);
	    if(pr>2){(void) fprintf(stdout,"rF");Cudd_PrintDebug(bdd,rF,n,pr);}
	    /* P(x) = \exists_{y}(F(x,y) \cdot new^l(y)) */
	    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, neW[l], x, y, n));
	    Cudd_Ref(P = Cudd_bddAndAbstract(bdd, *F, p, ycube));
	    Cudd_RecursiveDeref(bdd,p);
	    /* rB(x) = P(x) \cdot \overline{reached(x)}) */
	    Cudd_Ref(rB = Cudd_bddAnd(bdd, P, Cudd_Not(reached)));
	    Cudd_RecursiveDeref(bdd,P);
	    if(pr>2){(void) fprintf(stdout,"rB");Cudd_PrintDebug(bdd,rB,n,pr);}
	    /* new^{l+1}(x) = rF(x) + rB(x) */
	    Cudd_Ref(neW[l+1] = Cudd_bddOr(bdd, rF, rB));
	    Cudd_RecursiveDeref(bdd,rB);
	    Cudd_RecursiveDeref(bdd,rF);
	    if(pr>0) {
		(void) fprintf(stdout,"new[%d]",l+1);
		Cudd_PrintDebug(bdd,neW[l+1],n,pr);
	    }
	} /* start next layer */
	if (l==MAXLAYER) (void) fprintf(stderr,"ERROR! MAXLAYER exceeded.\n");
	exit(3);
endLayers:
	maximal_push(bdd, l-1, U, F, x, y, z, n, pryz, prxz, &stats);
	for (j = 0; j < l; j++) {
	    Cudd_RecursiveDeref(bdd,U[j]);
	    Cudd_RecursiveDeref(bdd,neW[j]);
	}
	Cudd_RecursiveDeref(bdd,neW[l]);
	if (pr > 0) {
	    Cudd_Ref(p = Cudd_bddAnd(bdd, sx, *F));
	    Ms=Cudd_CountMinterm(bdd, p, n<<1);
	    (void) fprintf(stdout,"# Flow out of s: %g\n", Ms);
	    Cudd_RecursiveDeref(bdd,p);
	}
	if (Cudd_bddLeq(bdd, fit, *F)) {
	    Cudd_Ref(*cut = fit);
	    goto endPhases;
	}
    } /* start next phase */
    if (i == MAXPHASE) (void) fprintf(stderr,"ERROR! MAXPHASE exceeded.\n");

    /* Last phase is completed --- print flow results. */
endPhases:
    Cudd_RecursiveDeref(bdd,tx);

    Cudd_Ref(q = Cudd_bddAnd(bdd, *F, sx));
    Ms = Cudd_CountMinterm(bdd, q, n<<1);
    Cudd_RecursiveDeref(bdd,q);

    Cudd_Ref(q = Cudd_bddAnd(bdd, *F, ty));
    Mt = Cudd_CountMinterm(bdd, q, n<<1);
    Cudd_RecursiveDeref(bdd,q);

    if (pr>1) (void) fprintf(stdout,"Mt= %g, Ms= %g \n", Mt, Ms);

    if (pr>3){(void) fprintf(stdout,"pryz");Cudd_PrintDebug(bdd,pryz,n*3,pr);}
    if (pr>3){(void) fprintf(stdout,"prxz");Cudd_PrintDebug(bdd,prxz,n*3,pr);}

    if (pr>0) {
	(void) fprintf(stdout,"#### Stats for maximum_flow ####\n");
	(void) fprintf(stdout,"%d variables %d of which x[i]\n", Cudd_ReadSize(bdd), n);
	(void) fprintf(stdout,"time       = %s\n",
		util_print_time(util_cpu_time() - stats.start_time));
	(void) fprintf(stdout,"phases     = %d\n", stats.phases);
	(void) fprintf(stdout,"layers     = %d\n", stats.layers);
	(void) fprintf(stdout,"FP iter.   = %d\n", stats.fpit);
    }

    Cudd_RecursiveDeref(bdd,fit);
    Cudd_RecursiveDeref(bdd,pryz);
    Cudd_RecursiveDeref(bdd,prxz);
    Cudd_RecursiveDeref(bdd,xcube);
    Cudd_RecursiveDeref(bdd,ycube);
    Cudd_RecursiveDeref(bdd,zcube);
#ifdef PRUNE
    Cudd_RecursiveDeref(bdd,E);
#endif

    FREE(U);
    FREE(neW);

    return(Ms);

} /* end of Ntr_maximum01Flow */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Selects set of edge-disjoint paths from layered network.]

  Description [Selects set of edge-disjoint paths from layered
  network.  maximal_pull is called when the BFS constructing the
  layered graph reaches a sink. At this point the new sets of the
  BFS have been formed, and we know every vertex in these sets is
  reachable from the source vertex (or vertices) s. The new sets are
  used to compute the set of useful edges exiting each layer to the
  right. In each layer, propagate_maximal_flow is called to select a
  maximal subset of these useful edges. This subset is then used to
  prune new and U.]

  SideEffects [None]

  SeeAlso     [maximal_push]

******************************************************************************/
static void
maximal_pull(
  DdManager * bdd /* manager */,
  int  l /* depth of layered network for current phase */,
  DdNode * ty /* sink node */,
  DdNode ** neW /* array of BFS layers */,
  DdNode ** U /* array of useful edges */,
  DdNode * E /* edge relation */,
  DdNode ** F /* flow relation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *p, *q, *r,
	   *UF, *UB;
    int	   m,
	   pr;		/* Print control */

    pr = stats->pr;

    /* The useful edges of the last layer are all the empty edges into
    ** the sink(s) from new[l].
    ** U^{l}(x,y) = t(y)\cdot \overline{F(x,y)}\cdot E(x,y)\cdot new^{l}(x)
    */
    Cudd_Ref(p = Cudd_bddAnd(bdd, E, Cudd_Not(*F)));
    Cudd_Ref(q = Cudd_bddAnd(bdd, neW[l], p));
    Cudd_RecursiveDeref(bdd,p);
    Cudd_Ref(U[l] = Cudd_bddAnd(bdd, ty, q));
    Cudd_RecursiveDeref(bdd,q);
    if(pr>1){(void) fprintf(stdout,"U[%d]",l);Cudd_PrintDebug(bdd,U[l],n<<1,pr);}
    /* Eliminate from new[l] the states with no paths to the sink(s).
    ** new^{l}(x)=\exists_y U^{l}(x,y)
    */
    Cudd_RecursiveDeref(bdd,neW[l]);
    Cudd_Ref(neW[l] = Cudd_bddExistAbstract(bdd, U[l], ycube));

    for (m = l; m >= 1; m--) {
	/* Find usable backward edges from level m-1 to level m.
	** UB(x,y) = new^{m}(x) \cdot F(x,y) \cdot new^{m-1}(y)
	*/
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, neW[m-1], x, y, n));
	Cudd_Ref(q = Cudd_bddAnd(bdd, r, *F));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_Ref(UB = Cudd_bddAnd(bdd, neW[m], q));
	Cudd_RecursiveDeref(bdd,q);
	if(pr>2){(void) fprintf(stdout,"UB");Cudd_PrintDebug(bdd,UB,n<<1,pr);}
	/* Find usable forward edges.
	** UF(x,y) = new^{m}(y) \cdot \overline{F(x,y)} \cdot E(x,y)
	** \cdot new^{m-1}(x)
	*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, E, Cudd_Not(*F)));
	Cudd_Ref(q = Cudd_bddAnd(bdd, neW[m-1], p));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, neW[m], x, y, n));
	Cudd_Ref(UF = Cudd_bddAnd(bdd, r, q));
	Cudd_RecursiveDeref(bdd,q);
	Cudd_RecursiveDeref(bdd,r);
	if(pr>2){(void) fprintf(stdout,"UF");Cudd_PrintDebug(bdd,UF,n<<1,pr);}
	/* U^{m-1}(x,y) = UB(y,x) + UF(x,y) */
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, UB, x, y, n));
	Cudd_RecursiveDeref(bdd,UB);
	Cudd_Ref(U[m-1] = Cudd_bddOr(bdd, UF, r));
	Cudd_RecursiveDeref(bdd,UF);
	Cudd_RecursiveDeref(bdd,r);
	if(pr>2){(void)fprintf(stdout,"U[%d]",m-1);
		Cudd_PrintDebug(bdd,U[m-1],n<<1,pr);}
	/* new[m-1](x) = \exists_{y}U^{m-1}(x,y) */
	Cudd_RecursiveDeref(bdd,neW[m-1]);
	Cudd_Ref(neW[m-1] = Cudd_bddExistAbstract(bdd, U[m-1], ycube));
	/* Compute maximal disjoint interlayer edge set. */
	propagate_maximal_flow(bdd, m, neW, U, x, y, z, n, pryz, prxz, stats);
	if(pr>0) {
	    (void)fprintf(stdout,"U[%d]",m-1);
	    Cudd_PrintDebug(bdd,U[m-1],n<<1,pr);
	}
    } /* prune next layer */

    return;

} /* end of maximal_pull */


/**Function********************************************************************

  Synopsis    [Pulls flow though a layer.]

  Description [Pulls flow though a layer. propagate_maximal_flow only
  affects U[m-1] and new[m-1].  At the end of this function, the edges
  in U[m] are guaranteed to drain all the flow supplied by the edges
  in U[m-1]. This effect is obtained by pruning U[m-1]. After the
  pruned U[m-1] is computed, new[m-1] is updated to keep track of what
  nodes are still useful.

  The pruning is performed without actually measuring the in-potential
  and the out-potential of each node. Instead, pairs of nodes from U[m-1]
  and U[m] are matched. To avoid counting, the procedure computes sets of
  paths that connect layer m-1 to layer m+1 and are edge-disjoint.

  Two paths from layer m-1 to layer m+1 are disjoint if they have distinct
  end-point or if they have distinct middle points. What condition to
  enforce depends on the "shape" of the layers.]

  SideEffects [Changes U[m-1] and new[m-1]]

  SeeAlso     [trellis rhombus hourglass]

******************************************************************************/
static void
propagate_maximal_flow(
  DdManager * bdd,
  int  m /* center of current bilayer */,
  DdNode ** neW /* array of reachable or useful nodes */,
  DdNode ** U /* array of usable or useful edges */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *rN;
    double   mtl, mtc, mtr;	/* minterms for left, center, right levels */
    int      pr;		/* print control */

    pr = stats->pr;

    mtl = Cudd_CountMinterm(bdd, neW[m-1], n);
    mtc = Cudd_CountMinterm(bdd, neW[m], n);

    /* rN(y) = \exists_x U^{m}(x,y) */
    Cudd_Ref(rN = Cudd_bddExistAbstract(bdd, U[m], xcube));
    mtr = Cudd_CountMinterm(bdd, rN, n);
    Cudd_RecursiveDeref(bdd,rN);

    if (pr > 0) {
	(void) fprintf(stdout, "layer = %d mtl = %g  mtc = %g  mtr = %g",
		       m, mtl, mtc, mtr);
    }

    if ((mtc > MANY_TIMES * mtl) || (mtc > MANY_TIMES * mtr)) {
	if (pr>0) (void) fprintf(stdout, " R\n");
	rhombus(bdd, m, neW, U, x, y, z, n, pryz, prxz, stats);
    } else if (mtr > MANY_TIMES * mtc) {
	if (pr>0) (void) fprintf(stdout, " H\n");
	hourglass(bdd, m, neW, U, x, y, z, n, pryz, prxz, stats);
    } else {
	if (pr>0) (void) fprintf(stdout, " T\n");
	trellis(bdd, m, neW, U, x, y, z, n, pryz, prxz, stats);
    }
    return;

} /* end of propagate_maximal_flow */


/**Function********************************************************************

  Synopsis    [Selects edges from a trellis-type bilayer.]

  Description [Selects edges from a trellis-type bilayer. Used to pull flow.
  First a matching is found in the left layer. Then the paths are extended
  (if possible) through the right layer. This process is repeated until a
  maximal flow is found.]

  SideEffects [None]

  SeeAlso     [rhombus hourglass trellisPush]

******************************************************************************/
static void
trellis(
  DdManager * bdd,
  int  m /* center level of current bilayer */,
  DdNode ** neW /* array of node levels */,
  DdNode ** U /* array of edge layers */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *p, *q, *r,
	     *Uin,		/* edges to be matched from U[m-1] */
	     *Uout,		/* edges to be matched from U[m] */
	     *P,
	     *LU, *RU,		/* left-unique and right-unique sets of edges */
	     *D,
	     *Ml, *Mr;		/* nodes matched from left and right */
    int      k,
	     pr;		/* print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}
    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(k = 0; k < MAXFPIT; k++) {
	stats->fpit++;
	/*LU(x,y)=Uin(x,y)\cdot\overline{\exists_{z}(Uin(z,y)\cdot\Pi(x,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uin, x, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, prxz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(LU = Cudd_bddAnd(bdd, Uin, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"LU");Cudd_PrintDebug(bdd,LU,n<<1,pr);}
	/*D(x,y)= LU(x,y)\cdot \overline{\exists_{z}(LU(x,z)\cdot \Pi(y,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, LU, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, pryz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(D = Cudd_bddAnd(bdd, LU, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,LU);
	if(pr>3){(void)fprintf(stdout,"D");Cudd_PrintDebug(bdd,D,n<<1,pr);}
	/*Ml(y)=\exists_{x}D(x,y)*/
	Cudd_Ref(Ml = Cudd_bddExistAbstract(bdd, D, xcube));
	if(pr>3){(void)fprintf(stdout,"Ml");Cudd_PrintDebug(bdd,Ml,n,pr);}
	/*P(x,y)=Ml(x)\cdot Uout(x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Ml, x, y, n));
	Cudd_Ref(P = Cudd_bddAnd(bdd, p, Uout));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Ml);
	if(pr>3){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n<<1,pr);}
	/*RU(x,y)= P(x,y)\cdot \overline{\exists_{z}(P(x,z)\cdot \Pi(y,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, pryz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(RU = Cudd_bddAnd(bdd, P, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,P);
	if(pr>3){(void)fprintf(stdout,"RU");Cudd_PrintDebug(bdd,RU,n<<1,pr);}
	/*Mr(x)=\exists_{y}RU(x,y)*/
	Cudd_Ref(Mr = Cudd_bddExistAbstract(bdd, RU, ycube));
	if(pr>3){(void)fprintf(stdout,"Mr");Cudd_PrintDebug(bdd,Mr,n,pr);}
	/*D(x,y)=D(x,y)\cdot Mr(y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Mr, x, y, n));
	Cudd_RecursiveDeref(bdd,Mr);
	Cudd_Ref(q = Cudd_bddAnd(bdd, D, p));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,D);
	D = q;
	if(pr>3){(void)fprintf(stdout,"D");Cudd_PrintDebug(bdd,D,n<<1,pr);}
	/*Uin(x,y)=Uin(x,y)-D(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uin, Cudd_Not(D)));
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = p;
	if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}
	/*Uout(x,y)=Uout(x,y)-RU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uout, Cudd_Not(RU)));
	Cudd_RecursiveDeref(bdd,Uout);
	Cudd_RecursiveDeref(bdd,RU);
	Uout = p;
	if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}
	/*\KW{if}(($D(x,y)=zero$)~~\KW{or}~~($Uin(x,y)=zero$)~~\KW{or}
	  ($Uout(x,y)=zero$))~~KW{break}*/
	if ((D == zero)||(Uin == zero)||(Uout == zero)) {
	    Cudd_RecursiveDeref(bdd,D);
	    break;
	}
	Cudd_RecursiveDeref(bdd,D);

    } /* Next least fixed point iteration with smaller Uin and Uout */
    if (k == MAXFPIT) (void) fprintf(stderr,
	"Trellis: WARNING! MAXFPIT (%d) exceeded processing Layer %d.\n",
	MAXFPIT, m);

    if (Uin != zero) {
	/* $U^{m-1}(x,y) = U^{m-1}(x,y)-Uin(x,y)$*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m-1], Cudd_Not(Uin)));
	Cudd_RecursiveDeref(bdd,U[m-1]);
	U[m-1] = p;
	/* $new^{m-1}(x,y) = \esists_yU^{m-1}(x,y)$*/
	Cudd_RecursiveDeref(bdd,neW[m-1]);
	Cudd_Ref(neW[m-1] = Cudd_bddExistAbstract(bdd, U[m-1], ycube));
    }
    if(pr>2){(void)fprintf(stdout,"U[%d]",m-1); Cudd_PrintDebug(bdd,U[m-1],n<<1,pr);}
    if(pr>2){(void)fprintf(stdout,"new[%d]",m-1);
		Cudd_PrintDebug(bdd,neW[m-1],n,pr);}

    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);

    return;

} /* end of trellis */


/**Function********************************************************************

  Synopsis    [Selects edges from a rhombus-type bilayer.]

  Description [Selects edges from a rhombus-type bilayer. Used to pull flow.
  Makes the left layer left-unique and the right layer right-unique. Prunes
  and repeats until convergence to a maximal flow. It makes sure that all
  intermediate points of the two-arc paths are disjoint at each iteration.]

  SideEffects [None]

  SeeAlso     [trellis hourglass rhombusPush]

******************************************************************************/
static void
rhombus(
  DdManager * bdd,
  int  m /* center of current bilayer */,
  DdNode ** neW,
  DdNode ** U /* arrays for flow propagation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *p, *q, *r,
	     *Uin,		/* edges to be matched from U[m-1] */
	     *Uout,		/* edges to be matched from U[m] */
	     *P,
	     *LU, *RU,		/* left-unique and right-unique sets of edges */
	     *Ml, *Mr;		/* nodes matched from left and right */
    int      k,
	     pr;		/* print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(k = 0; k < MAXFPIT; k++) {
	stats->fpit++;
	/*LU(x,y)=Uin(x,y)\cdot\overline{\exists_{z}(Uin(z,y)\cdot\Pi(x,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uin, x, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, prxz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(LU = Cudd_bddAnd(bdd, Uin, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"LU");Cudd_PrintDebug(bdd,LU,n<<1,pr);}
	/*Ml(y)=\exists_{x}LU(x,y)*/
	Cudd_Ref(Ml = Cudd_bddExistAbstract(bdd, LU, xcube));
	if(pr>3){(void)fprintf(stdout,"Ml");Cudd_PrintDebug(bdd,Ml,n,pr);}
	/*P(x,y)=Ml(x)\cdot Uout(x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Ml, x, y, n));
	Cudd_Ref(P = Cudd_bddAnd(bdd, p, Uout));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Ml);
	if(pr>3){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n<<1,pr);}
	/*RU(x,y)= P(x,y)\cdot \overline{\exists_{z}(P(x,z)\cdot \Pi(y,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, pryz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(RU = Cudd_bddAnd(bdd, P, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,P);
	if(pr>3){(void)fprintf(stdout,"RU");Cudd_PrintDebug(bdd,RU,n<<1,pr);}
	/*Mr(x)=\exists_{y}RU(x,y)*/
	Cudd_Ref(Mr = Cudd_bddExistAbstract(bdd, RU, ycube));
	if(pr>3){(void)fprintf(stdout,"Mr");Cudd_PrintDebug(bdd,Mr,n,pr);}
	/*LU(x,y)=LU(x,y)\cdot Mr(y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Mr, x, y, n));
	Cudd_RecursiveDeref(bdd,Mr);
	Cudd_Ref(q = Cudd_bddAnd(bdd, LU, p));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,LU);
	LU = q;
	if(pr>3){(void)fprintf(stdout,"LU");Cudd_PrintDebug(bdd,LU,n<<1,pr);}
	/*Uin(x,y)=Uin(x,y)-LU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uin, Cudd_Not(LU)));
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = p;
	if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}
	/*Uout(x,y)=Uout(x,y)-RU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uout, Cudd_Not(RU)));
	Cudd_RecursiveDeref(bdd,Uout);
	Cudd_RecursiveDeref(bdd,RU);
	Uout = p;
	if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}
	/*\KW{if}(($LU(x,y)=zero$)~~\KW{or}~~($Uin(x,y)=zero$)~~\KW{or}
	  ($Uout(x,y)=zero$))~~KW{break}*/
	if((LU == zero)||(Uin == zero)||(Uout == zero)) {
	    Cudd_RecursiveDeref(bdd,LU);
	    break;
	}
	Cudd_RecursiveDeref(bdd,LU);

    } /* Next least fixed point iteration with smaller Uin and Uout */
    if (k == MAXFPIT) (void) fprintf(stderr,
	"Rhombus: WARNING! MAXFPIT (%d) exceeded processing Layer %d.\n",
	MAXFPIT, m);

    if (Uin != zero) {
	/* $U^{m-1}(x,y) = U^{m-1}(x,y)-Uin(x,y)$*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m-1], Cudd_Not(Uin)));
	Cudd_RecursiveDeref(bdd,U[m-1]);
	U[m-1] = p;
	/* $new^{m-1}(x,y) = \esists_yU^{m-1}(x,y)$*/
	Cudd_RecursiveDeref(bdd,neW[m-1]);
	Cudd_Ref(neW[m-1] = Cudd_bddExistAbstract(bdd, U[m-1], ycube));
    }
    if(pr>2){(void)fprintf(stdout,"U[%d]",m-1); Cudd_PrintDebug(bdd,U[m-1],n<<1,pr);}
    if(pr>2){
	(void)fprintf(stdout,"new[%d]",m-1);
	Cudd_PrintDebug(bdd,neW[m-1],n,pr);
    }
    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);

    return;

} /* end of rhombus */


/**Function********************************************************************

  Synopsis    [Selects edges from a hourglass-type bilayer.]

  Description [Selects edges from a hourglass-type bilayer. Used to
  pull flow.  Method described in paper. More general, but more
  expensive than the others.]

  SideEffects [None]

  SeeAlso     [trellis rhombus hourglassPush]

******************************************************************************/
static void
hourglass(
  DdManager * bdd,
  int  m /* center level of current bilayer */,
  DdNode ** neW,
  DdNode ** U /* arrays for flow propagation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *przy,
	     *p, *q, *r,
	     *Uin,		/* edges to be matched from U[m-1] */
	     *Uout,		/* edges to be matched from U[m] */
	     *P, *Q,
	     *PA, *D;
    int      k,
	     pr;		/* print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /* Build priority function. */
    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, pryz, y, z, n));
    Cudd_Ref(przy = Cudd_bddAdjPermuteX(bdd,p,x,n));
    Cudd_RecursiveDeref(bdd,p);
    if(pr>2){(void)fprintf(stdout,"przy");Cudd_PrintDebug(bdd,przy,n*3,pr);}

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>1){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>1){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(k = 0; k < MAXFPIT; k++) {
	stats->fpit++;
	/*P(x,y,z)=Uin(x,y)\cdot Uout(y,z)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uout, y, z, n));
	if(pr>2){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddSwapVariables(bdd, p, x, y, n));
	Cudd_RecursiveDeref(bdd,p);
	if(pr>2){(void)fprintf(stdout,"q");Cudd_PrintDebug(bdd,q,n<<1,pr);}
	Cudd_Ref(P = Cudd_bddAnd(bdd, Uin, q));
	Cudd_RecursiveDeref(bdd,q);
	if(pr>1){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n*3,pr);}
	/*PA(x,z)=\exists_yP(x,y,z)*/
	Cudd_Ref(PA = Cudd_bddExistAbstract(bdd, P, ycube));
	if(pr>2){(void)fprintf(stdout,"PA");Cudd_PrintDebug(bdd,PA,n<<1,pr);}
	if(pr>3) {
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, PA, xcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, PA, zcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	}
	/*Q(x,z)= PA(x,z)\cdot \overline{\exists_{y}(PA(x,y)\cdot \Pi(z,y))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, PA, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, przy, ycube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(Q = Cudd_bddAnd(bdd, PA, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,PA);
	if(pr>2){(void)fprintf(stdout,"Q");Cudd_PrintDebug(bdd,Q,n<<1,pr);}
	if(pr>3) {
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, Q, xcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	}
	/*D(x,z)= Q(x,z)\cdot \overline{\exists_{y}(Q(y,z)\cdot \Pi(x,y))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Q, x, y, n));
	Cudd_Ref(q = Cudd_bddSwapVariables(bdd, prxz, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, q, ycube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,q);
	Cudd_Ref(D = Cudd_bddAnd(bdd, Q, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,Q);
	if(pr>1){(void)fprintf(stdout,"D");Cudd_PrintDebug(bdd,D,n<<1,pr);}
	/*P(x,y,z)=P(x,y,z)\cdot D(x,z)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, P, D));
	Cudd_RecursiveDeref(bdd,D);
	Cudd_RecursiveDeref(bdd,P);
	P = p;
	if(pr>2){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n*3,pr);}
	/*Uin(x,y)=Uin(x,y)-\exists_zP(x,y,z)*/
	Cudd_Ref(p = Cudd_bddExistAbstract(bdd, P, zcube));
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddAnd(bdd, Uin, Cudd_Not(p)));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = q;
	if(pr>1){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}
	/*Uout(x,y)=Uout(x,y)-\exists_zP(z,x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, x, y, n));
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n*3,pr);}
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, p, y, z, n));
	Cudd_RecursiveDeref(bdd,p);
	if(pr>3){(void)fprintf(stdout,"r");Cudd_PrintDebug(bdd,r,n*3,pr);}
	Cudd_Ref(p = Cudd_bddExistAbstract(bdd, r, zcube));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddAnd(bdd, Uout, Cudd_Not(p)));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Uout);
	Uout = q;
	if(pr>1){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}
	/*\KW{if}(($P(x,y,z)=zero$)~~\KW{or}~~($Uin(x,y)=zero$)~~\KW{or}
	  ($Uout(x,y)=zero$))~~KW{break}*/
	if((P == zero)||(Uin == zero)||(Uout == zero)) {
	    Cudd_RecursiveDeref(bdd,P);
	    break;
	}
	Cudd_RecursiveDeref(bdd,P);

    } /* Next least fixed point iteration with smaller P */
    if (k == MAXFPIT) (void) fprintf(stderr,
	"Hourglass: WARNING! MAXFPIT (%d) exceeded processing Layer %d.\n",
	MAXFPIT, m);

    if (Uin != zero) {
	/* $U^{m-1}(x,y) = U^{m-1}(x,y)-Uin(x,y)$*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m-1], Cudd_Not(Uin)));
	Cudd_RecursiveDeref(bdd,U[m-1]);
	U[m-1] = p;
	/* $new^{m-1}(x,y) = \esists_yU^{m-1}(x,y)$*/
	Cudd_RecursiveDeref(bdd,neW[m-1]);
	Cudd_Ref(neW[m-1] = Cudd_bddExistAbstract(bdd, U[m-1], ycube));
    }
    if(pr>1){(void)fprintf(stdout,"U[%d]",m-1); Cudd_PrintDebug(bdd,U[m-1],n<<1,pr);}
    if(pr>1){(void)fprintf(stdout,"new[%d]",m-1);
	     Cudd_PrintDebug(bdd,neW[m-1],n,pr);}

    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);
    Cudd_RecursiveDeref(bdd,przy);

    return;

} /* end of hourglass */


/**Function********************************************************************

  Synopsis    [Pushes flow through useful edges.]

  Description [Pushes flow from the source(s) to the sink(s) through
  useful edges.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static void
maximal_push(
  DdManager * bdd,
  int  l /* Depth of layered network for current phase */,
  DdNode ** U /* array of edge sets for flow propagation */,
  DdNode ** F /* edge and flow relations */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* arrays of variables for rows and columns */,
  int  n /* number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* priority functions */,
  flowStats * stats)
{
    DdNode *p, *q, *r,
	   *UT,
	   *lN, *cN, *rN; /* left, center, right nodes of bilayer */
    double mtl, mtc, mtr;
    int    m,
	   pr;	  /* print control */

    pr = stats->pr;

    if (l == 0) {
	/* F(x,y) = F(x,y) + U^{0}(x,y) */
	Cudd_Ref(q = Cudd_bddOr(bdd, *F, U[0]));
	Cudd_RecursiveDeref(bdd,*F);
	*F = q;
	if(pr>3){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}
	return;
    }

    for (m = 1; m < l; m++) {
	/* lN(x) = \exists_y U^{m-1}(x,y) */
	Cudd_Ref(lN = Cudd_bddExistAbstract(bdd, U[m-1], ycube));
	mtl = Cudd_CountMinterm(bdd, lN, n);
	Cudd_RecursiveDeref(bdd,lN);

	/* cN(y) = \exists_x U^{m-1}(x,y) */
	Cudd_Ref(cN = Cudd_bddExistAbstract(bdd, U[m-1], xcube));
	mtc = Cudd_CountMinterm(bdd, cN, n);
	Cudd_RecursiveDeref(bdd,cN);

	/* rN(y) = \exists_x U^{m}(x,y) */
	Cudd_Ref(rN = Cudd_bddExistAbstract(bdd, U[m], xcube));
	mtr = Cudd_CountMinterm(bdd, rN, n);
	Cudd_RecursiveDeref(bdd,rN);

	if (pr > 0) {
	    (void) fprintf(stdout, "layer = %d mtl = %g  mtc = %g  mtr = %g",
			   m, mtl, mtc, mtr);
	}
	if ((mtc > MANY_TIMES * mtl) && !(mtr > MANY_TIMES * mtl)) {
	    if (pr>0) (void) fprintf(stdout, " R\n");
	    rhombusPush(bdd, m, U, x, y, z, n, pryz, prxz, stats);
	} else if (mtl > MANY_TIMES * mtc) {
	    if (pr>0) (void) fprintf(stdout, " H\n");
	    hourglassPush(bdd, m, U, x, y, z, n, pryz, prxz, stats);
	} else {
	    if (pr>0) (void) fprintf(stdout, " T\n");
	    trellisPush(bdd, m, U, x, y, z, n, pryz, prxz, stats);
	}

	/* F(x,y) = F(x,y) + U^{m-1}(x,y) \cdot \overline{F(y,x)} */
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, *F, x, y, n));
	Cudd_Ref(q = Cudd_bddAnd(bdd, Cudd_Not(p), U[m-1]));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(r = Cudd_bddOr(bdd, *F, q));
	Cudd_RecursiveDeref(bdd,q);
	Cudd_RecursiveDeref(bdd,*F);
	*F = r;
	if(pr>3){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

	/* F(x,y) = F(x,y) - U^{m-1}(y,x) */
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, U[m-1], x, y, n));
	Cudd_Ref(q = Cudd_bddAnd(bdd, *F, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,*F);
	*F = q;
	if(pr>3){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

    } /* Push maximal flow to next layer */

    /*F(x,y)=F(x,y)+U^{l-1}(x,y)\cdot\overline{F(y,x)}*/
    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, *F, x, y, n));
    Cudd_Ref(q = Cudd_bddAnd(bdd, Cudd_Not(p), U[l-1]));
    Cudd_RecursiveDeref(bdd,p);
    Cudd_Ref(r = Cudd_bddOr(bdd, *F, q));
    Cudd_RecursiveDeref(bdd,q);
    Cudd_RecursiveDeref(bdd,*F);
    *F = r;
    if(pr>3){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

    /*F(y,x)=F(y,x)-U^{l-1}(x,y)*/
    Cudd_Ref(r = Cudd_bddSwapVariables(bdd, U[l-1], x, y, n));
    Cudd_Ref(q = Cudd_bddAnd(bdd, *F, Cudd_Not(r)));
    Cudd_RecursiveDeref(bdd,r);
    Cudd_RecursiveDeref(bdd,*F);
    *F = q;
    if(pr>1){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

    /*UT(x,y)=\exists_y(U^{l-1}(y,x))\cdot U^{l}(x,y)*/
    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, U[l-1], xcube));
    if(pr>4){(void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);}
    Cudd_Ref(q = Cudd_bddSwapVariables(bdd, p, x, y, n));
    Cudd_RecursiveDeref(bdd,p);
    if(pr>4){(void) fprintf(stdout,"q");Cudd_PrintDebug(bdd,q,n,pr);}
    Cudd_Ref(UT = Cudd_bddAnd(bdd, U[l], q));
    Cudd_RecursiveDeref(bdd,q);
    if(pr>2){(void) fprintf(stdout,"UT");Cudd_PrintDebug(bdd,UT,n<<1,pr);}

    /*F(x,y)=F(x,y)+UT(x,y)\cdot\overline{F(y,x)}*/
    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, *F, x, y, n));
    Cudd_Ref(q = Cudd_bddAnd(bdd, Cudd_Not(p), UT));
    Cudd_RecursiveDeref(bdd,p);
    Cudd_Ref(r = Cudd_bddOr(bdd, *F, q));
    Cudd_RecursiveDeref(bdd,q);
    Cudd_RecursiveDeref(bdd,*F);
    *F = r;
    if(pr>3){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

    /*F(y,x)=F(y,x)-UT(x,y)*/
    Cudd_Ref(r = Cudd_bddSwapVariables(bdd, UT, x, y, n));
    Cudd_RecursiveDeref(bdd,UT);
    Cudd_Ref(q = Cudd_bddAnd(bdd, *F, Cudd_Not(r)));
    Cudd_RecursiveDeref(bdd,r);
    Cudd_RecursiveDeref(bdd,*F);
    *F = q;
    if(pr>1){(void) fprintf(stdout,"F");Cudd_PrintDebug(bdd,*F,n<<1,pr);}

    return;

} /* end of maximal_push */


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static void
trellisPush(
  DdManager * bdd,
  int  m /* Current layer */,
  DdNode ** U /* Array of edge sets for flow propagation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* Arrays of variables for rows and columns */,
  int  n /* Number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* Priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *p, *r,
	     *Uin,              /* Edges to be matched from U[m-1] */
	     *Uout,             /* Edges to be matched from U[m] */
	     *RU, *LU,
	     *P,
	     *Ml;

    int      i,
	     pr;	  /* Print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(i=0; i<MAXFPIT; i++) {
	stats->fpit++;
	/*LU(x,y)=Uin(x,y)\cdot\overline{\exists_{z}(Uin(z,y)\cdot\Pi(x,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uin, x, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, prxz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(LU = Cudd_bddAnd(bdd, Uin, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"LU");Cudd_PrintDebug(bdd,LU,n<<1,pr);}

	/*Ml(y)=\exists_{x}LU(x,y)*/
	Cudd_Ref(Ml = Cudd_bddExistAbstract(bdd, LU, xcube));
	if(pr>3){(void)fprintf(stdout,"Ml");Cudd_PrintDebug(bdd,Ml,n,pr);}

	/*P(x,y)=Ml(x)\cdot Uout(x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Ml, x, y, n));
	Cudd_Ref(P = Cudd_bddAnd(bdd, p, Uout));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Ml);
	if(pr>3){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n<<1,pr);}

	/*RU(x,y)= P(x,y)\cdot \overline{\exists_{z}(P(x,z)\cdot \Pi(y,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, pryz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(RU = Cudd_bddAnd(bdd, P, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,P);
	if(pr>3){(void)fprintf(stdout,"RU");Cudd_PrintDebug(bdd,RU,n<<1,pr);}

	/*Uin(x,y)=Uin(x,y)-LU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uin, Cudd_Not(LU)));
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = p;
	if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

	/*Uout(x,y)=Uout(x,y)-RU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uout, Cudd_Not(RU)));
	Cudd_RecursiveDeref(bdd,Uout);
	Cudd_RecursiveDeref(bdd,RU);
	Uout = p;
	if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

	/*\KW{if}(($LU(x,y)=zero$)~~\KW{or}~~($Uin(x,y)=zero$))~~KW{break}*/
	if((LU == zero)||(Uin == zero)) {
	    Cudd_RecursiveDeref(bdd,LU);
	    break;
	}

	Cudd_RecursiveDeref(bdd,LU);

    } /* Next least fixed point iteration with smaller Uin and Uout */
    if (i == MAXFPIT) (void) fprintf(stderr,
	"TrellisPush: ERROR! MAXFPIT (%d) exceeded at layer %d.\n",
	MAXFPIT, m);

    /* $U^{m}(x,y) = U^{m}(x,y)-Uout(x,y)$*/
    if (Uout != zero) {
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m], Cudd_Not(Uout)));
	Cudd_RecursiveDeref(bdd,U[m]);
	U[m] = p;
	if(pr>3){(void)fprintf(stdout,"U[%d]",m);
	    Cudd_PrintDebug(bdd,U[m],n<<1,pr);}
    }

    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);

} /* end of trellisPush */


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static void
rhombusPush(
  DdManager * bdd,
  int  m /* Current layer */,
  DdNode ** U /* Array of edge sets for flow propagation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* Arrays of variables for rows and columns */,
  int  n /* Number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* Priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *p, *r,
	     *Uin,              /* Edges to be matched from U[m-1] */
	     *Uout,             /* Edges to be matched from U[m] */
	     *RU, *LU,
	     *P,
	     *Ml;

    int      i,
	     pr;	  /* Print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(i = 0; i < MAXFPIT; i++) {
	stats->fpit++;
	/*RU(x,y)=Uin(x,y)\cdot\overline{\exists_{z}(Uin(x,z)\cdot\Pi(y,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uin, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, pryz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(RU = Cudd_bddAnd(bdd, Uin, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"RU");Cudd_PrintDebug(bdd,RU,n<<1,pr);}

	/*Ml(y)=\exists_{x}RU(x,y)*/
	Cudd_Ref(Ml = Cudd_bddExistAbstract(bdd, RU, xcube));
	if(pr>3){(void)fprintf(stdout,"Ml");Cudd_PrintDebug(bdd,Ml,n,pr);}

	/*P(x,y)=Ml(x)\cdot Uout(x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Ml, x, y, n));
	Cudd_Ref(P = Cudd_bddAnd(bdd, p, Uout));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Ml);
	if(pr>3){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n<<1,pr);}

	/*LU(x,y)= P(x,y)\cdot \overline{\exists_{z}(P(z,y)\cdot \Pi(x,z))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, x, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, prxz, zcube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(LU = Cudd_bddAnd(bdd, P, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,P);
	if(pr>3){(void)fprintf(stdout,"LU");Cudd_PrintDebug(bdd,LU,n<<1,pr);}

	/*Uin(x,y)=Uin(x,y)-RU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uin, Cudd_Not(RU)));
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = p;
	if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

	/*Uout(x,y)=Uout(x,y)-LU(x,y)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, Uout, Cudd_Not(LU)));
	Cudd_RecursiveDeref(bdd,Uout);
	Cudd_RecursiveDeref(bdd,LU);
	Uout = p;
	if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

	/*\KW{if}(($RU(x,y)=zero$)~~\KW{or}~~($Uin(x,y)=zero$))~~KW{break}*/
	if((RU == zero)||(Uin == zero)) {
	    Cudd_RecursiveDeref(bdd,RU);
	    break;
	}

	Cudd_RecursiveDeref(bdd,RU);

    } /* Next least fixed point iteration with smaller Uin and Uout */
    if (i == MAXFPIT) (void) fprintf(stderr,
	"RhombusPush: ERROR! MAXFPIT (%d) exceeded at layer %d.\n",
	MAXFPIT, m);

    /* $U^{m}(x,y) = U^{m}(x,y)-Uout(x,y)$*/
    if (Uout != zero) {
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m], Cudd_Not(Uout)));
	Cudd_RecursiveDeref(bdd,U[m]);
	U[m] = p;
	if(pr>3){(void)fprintf(stdout,"U[%d]",m);
	    Cudd_PrintDebug(bdd,U[m],n<<1,pr);}
    }

    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);

    return;

} /* end of rhombusPush */


/**Function********************************************************************

  Synopsis    []

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static void
hourglassPush(
  DdManager * bdd,
  int  m /* Current layer */,
  DdNode ** U /* Array of edge sets for flow propagation */,
  DdNode ** x,
  DdNode ** y,
  DdNode ** z /* Arrays of variables for rows and columns */,
  int  n /* Number of x variables */,
  DdNode * pryz,
  DdNode * prxz /* Priority functions */,
  flowStats * stats)
{
    DdNode *one, *zero,
	     *przy,
	     *p, *q, *r,
	     *Uin,              /* Edges to be matched from U[m-1] */
	     *Uout,             /* Edges to be matched from U[m] */
	     *P, *Q,
	     *PA, *D;

    int      i,
	     pr;	  /* Print control */

    pr = stats->pr;

    one = Cudd_ReadOne(bdd);
    zero = Cudd_Not(one);

    /* Build priority function. */
    Cudd_Ref(p = Cudd_bddSwapVariables(bdd, pryz, y, z, n));
    Cudd_Ref(przy = Cudd_bddAdjPermuteX(bdd,p,x,n));
    Cudd_RecursiveDeref(bdd,p);
    if(pr>2){(void)fprintf(stdout,"przy");Cudd_PrintDebug(bdd,przy,n*3,pr);}

    /*Uout(x,y)=U^m(x,y)*/
    Cudd_Ref(Uout = U[m]);
    if(pr>3){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

    /*Uin(x,y)=U^{m-1}(x,y)*/
    Cudd_Ref(Uin = U[m-1]);
    if(pr>3){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

    for(i = 0; i < MAXFPIT; i++) {
	stats->fpit++;
	/*P(x,y,z)=Uin(x,y)\cdot Uout(y,z)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Uout, y, z, n));
	if(pr>2){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddSwapVariables(bdd, p, x, y, n));
	Cudd_RecursiveDeref(bdd,p);
	if(pr>2){(void)fprintf(stdout,"q");Cudd_PrintDebug(bdd,q,n<<1,pr);}
	Cudd_Ref(P = Cudd_bddAnd(bdd, Uin, q));
	Cudd_RecursiveDeref(bdd,q);
	if(pr>1){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n*3,pr);}

	/*PA(x,z)=\exists_yP(x,y,z)*/
	Cudd_Ref(PA = Cudd_bddExistAbstract(bdd, P, ycube));
	if(pr>2){(void)fprintf(stdout,"PA");Cudd_PrintDebug(bdd,PA,n<<1,pr);}
	if(pr>3) {
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, PA, xcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, PA, zcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	}

	/*Q(x,z)= PA(x,z)\cdot \overline{\exists_{y}(PA(x,y)\cdot \Pi(z,y))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, PA, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, przy, ycube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_Ref(Q = Cudd_bddAnd(bdd, PA, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,PA);
	if(pr>2){(void)fprintf(stdout,"Q");Cudd_PrintDebug(bdd,Q,n<<1,pr);}
	if(pr>3) {
	    Cudd_Ref(p = Cudd_bddExistAbstract(bdd, Q, xcube));
	    (void) fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n,pr);
	    Cudd_RecursiveDeref(bdd,p);
	}

	/*D(x,z)= Q(x,z)\cdot \overline{\exists_{y}(Q(y,z)\cdot \Pi(x,y))}*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, Q, x, y, n));
	Cudd_Ref(q = Cudd_bddSwapVariables(bdd, prxz, y, z, n));
	Cudd_Ref(r = Cudd_bddAndAbstract(bdd, p, q, ycube));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,q);
	Cudd_Ref(D = Cudd_bddAnd(bdd, Q, Cudd_Not(r)));
	Cudd_RecursiveDeref(bdd,r);
	Cudd_RecursiveDeref(bdd,Q);
	if(pr>1){(void)fprintf(stdout,"D");Cudd_PrintDebug(bdd,D,n<<1,pr);}

	/*P(x,y,z)=P(x,y,z)\cdot D(x,z)*/
	Cudd_Ref(p = Cudd_bddAnd(bdd, P, D));
	Cudd_RecursiveDeref(bdd,D);
	Cudd_RecursiveDeref(bdd,P);
	P = p;
	if(pr>2){(void)fprintf(stdout,"P");Cudd_PrintDebug(bdd,P,n*3,pr);}

	/*Uin(x,y)=Uin(x,y)-\exists_zP(x,y,z)*/
	Cudd_Ref(p = Cudd_bddExistAbstract(bdd, P, zcube));
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddAnd(bdd, Uin, Cudd_Not(p)));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Uin);
	Uin = q;
	if(pr>1){(void)fprintf(stdout,"Uin");Cudd_PrintDebug(bdd,Uin,n<<1,pr);}

	/*Uout(x,y)=Uout(x,y)-\exists_zP(z,x,y)*/
	Cudd_Ref(p = Cudd_bddSwapVariables(bdd, P, x, y, n));
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n*3,pr);}
	Cudd_Ref(r = Cudd_bddSwapVariables(bdd, p, y, z, n));
	Cudd_RecursiveDeref(bdd,p);
	if(pr>3){(void)fprintf(stdout,"r");Cudd_PrintDebug(bdd,r,n*3,pr);}
	Cudd_Ref(p = Cudd_bddExistAbstract(bdd, r, zcube));
	Cudd_RecursiveDeref(bdd,r);
	if(pr>3){(void)fprintf(stdout,"p");Cudd_PrintDebug(bdd,p,n<<1,pr);}
	Cudd_Ref(q = Cudd_bddAnd(bdd, Uout, Cudd_Not(p)));
	Cudd_RecursiveDeref(bdd,p);
	Cudd_RecursiveDeref(bdd,Uout);
	Uout = q;
	if(pr>1){(void)fprintf(stdout,"Uout");Cudd_PrintDebug(bdd,Uout,n<<1,pr);}

	/*\KW{if}(($P(x,y,z)=zero$)~~\KW{or}~~($Uin(x,y)=zero$)~~\KW{or}
	  ($Uout(x,y)=zero$))~~KW{break}*/
	if((P == zero)||(Uin == zero)||(Uout == zero)) {
	    Cudd_RecursiveDeref(bdd,P);
	    break;
	}

	Cudd_RecursiveDeref(bdd,P);

    } /* Next least fixed point iteration with smaller P */
    if (i == MAXFPIT) (void) fprintf(stderr,
	"HourglassPush: ERROR! MAXFPIT (%d) exceeded at layer %d.\n",
	MAXFPIT, m);

    /* $U^{m}(x,y) = U^{m}(x,y)-Uout(x,y)$*/
    if (Uout != zero) {
	Cudd_Ref(p = Cudd_bddAnd(bdd, U[m], Cudd_Not(Uout)));
	Cudd_RecursiveDeref(bdd,U[m]);
	U[m] = p;
    }
    if(pr>1){(void)fprintf(stdout,"U[%d]",m); Cudd_PrintDebug(bdd,U[m],n<<1,pr);}

    Cudd_RecursiveDeref(bdd,Uin);
    Cudd_RecursiveDeref(bdd,Uout);
    Cudd_RecursiveDeref(bdd,przy);

    return;

} /* end of hourglassPush */
