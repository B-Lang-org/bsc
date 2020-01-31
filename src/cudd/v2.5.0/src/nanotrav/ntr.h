/**CHeaderFile*****************************************************************

  FileName    [ntr.h]

  PackageName [ntr]

  Synopsis    [Simple-minded package to do traversal.]

  Description []

  SeeAlso     []

  Author      [Fabio Somenzi]

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

  Revision    [$Id: ntr.h,v 1.28 2012/02/05 01:53:01 fabio Exp fabio $]

******************************************************************************/

#ifndef _NTR
#define _NTR

/*---------------------------------------------------------------------------*/
/* Nested includes                                                           */
/*---------------------------------------------------------------------------*/

#include "dddmp.h"
#include "bnet.h"

#ifdef __cplusplus
extern "C" {
#endif

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define PI_PS_FROM_FILE	0
#define PI_PS_DFS	1
#define PI_PS_GIVEN	2

#define NTR_IMAGE_MONO 0
#define NTR_IMAGE_PART 1
#define NTR_IMAGE_CLIP 2
#define NTR_IMAGE_DEPEND 3

#define NTR_UNDER_APPROX 0
#define NTR_OVER_APPROX 1

#define NTR_FROM_NEW 0
#define NTR_FROM_REACHED 1
#define NTR_FROM_RESTRICT 2
#define NTR_FROM_COMPACT 3
#define NTR_FROM_SQUEEZE 4
#define NTR_FROM_UNDERAPPROX 5
#define NTR_FROM_OVERAPPROX 6

#define NTR_GROUP_NONE 0
#define NTR_GROUP_DEFAULT 1
#define NTR_GROUP_FIXED 2

#define NTR_SHORT_NONE 0
#define NTR_SHORT_BELLMAN 1
#define NTR_SHORT_FLOYD 2
#define NTR_SHORT_SQUARE 3

/*---------------------------------------------------------------------------*/
/* Stucture declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Type declarations                                                         */
/*---------------------------------------------------------------------------*/

typedef	struct	NtrOptions {
    long	initialTime;	/* this is here for convenience */
    int		verify;		/* read two networks and compare them */
    char	*file1;		/* first network file name */
    char	*file2;		/* second network file name */
    int		second;		/* a second network is given */
    int		traverse;	/* do reachability analysis */
    int		depend;		/* do latch dependence analysis */
    int		image;		/* monolithic, partitioned, or clip */
    double	imageClip;	/* clipping depth in image computation */
    int		approx;		/* under or over approximation */
    int		threshold;	/* approximation threshold */
    int		from;		/* method to compute from states */
    int		groupnsps;	/* group present state and next state vars */
    int		closure;	/* use transitive closure */
    double	closureClip;	/* clipping depth in closure computation */
    int		envelope;	/* compute outer envelope */
    int		scc;		/* compute strongly connected components */
    int		zddtest;	/* do zdd test */
    int		printcover;	/* print ISOP covers when testing ZDDs */
    int		maxflow;	/* compute maximum flow in network */
    int		shortPath;	/* compute shortest paths in network */
    int		selectiveTrace;	/* use selective trace in shortest paths */
    char	*sinkfile;	/* file for externally provided sink node */
    int		partition;	/* test McMillan conjunctive partitioning */
    int		char2vect;	/* test char-to-vect decomposition */
    int		density;	/* test density-related functions */
    double	quality;	/* quality parameter for density functions */
    int		decomp;		/* test decomposition functions */
    int		cofest;		/* test cofactor estimation */
    double	clip;		/* test clipping functions */
    int		dontcares;	/* test equivalence and containment with DCs */
    int		closestCube;	/* test Cudd_bddClosestCube */
    int		clauses;	/* test extraction of two-literal clauses */
    int		noBuild;	/* do not build BDDs; just echo order */
    int		stateOnly;	/* ignore primary outputs */
    char	*node;		/* only node for which to build BDD */
    int		locGlob;	/* build global or local BDDs */
    int		progress;	/* report output names while building BDDs */
    int		cacheSize;	/* computed table initial size */
    unsigned long maxMemory;	/* target maximum memory */
    unsigned long maxMemHard;	/* maximum allowed memory */
    unsigned int maxLive;	/* maximum number of nodes */
    int		slots;		/* unique subtable initial slots */
    int		ordering;	/* FANIN DFS ... */
    char	*orderPiPs;	/* file for externally provided order */
    Cudd_ReorderingType	reordering; /* NONE RANDOM PIVOT SIFTING ... */
    int		autoDyn;	/* ON OFF */
    Cudd_ReorderingType autoMethod; /* RANDOM PIVOT SIFTING CONVERGE ... */
    char	*treefile;	/* file name for variable tree */
    int		firstReorder;	/* when to do first reordering */
    int		countDead;	/* count dead nodes toward triggering
				   reordering */
    int		maxGrowth;	/* maximum growth during reordering (%) */
    Cudd_AggregationType groupcheck; /* grouping function */
    int		arcviolation;   /* percent violation of arcs in
				   extended symmetry check */
    int		symmviolation;  /* percent symm violation in
				   extended symmetry check */
    int		recomb;		/* recombination parameter for grouping */
    int		nodrop;		/* don't drop intermediate BDDs ASAP */
    int		signatures;	/* computation of signatures */
    int		gaOnOff;	/* whether to run GA at the end */
    int		populationSize;	/* population size for GA */
    int		numberXovers;	/* number of crossovers for GA */
    int		bdddump;	/* ON OFF */
    int		dumpFmt;	/* 0 -> dot 1 -> blif 2 ->daVinci 3 -> DDcal
				** 4 -> factored form */
    char	*dumpfile;	/* filename for dump */
    int		store;		/* iteration at which to store Reached */
    char	*storefile;	/* filename for storing Reached */
    int		load;		/* load initial states from file */
    char	*loadfile;	/* filename for loading states */
    int		verb;		/* level of verbosity */
} NtrOptions;

typedef struct NtrHeapSlot {
    void *item;
    int key;
} NtrHeapSlot;

typedef struct NtrHeap {
    int size;
    int nslots;
    NtrHeapSlot *slots;
} NtrHeap;

typedef struct NtrPartTR {
    int nparts;			/* number of parts */
    DdNode **part;		/* array of parts */
    DdNode **icube;		/* quantification cubes for image */
    DdNode **pcube;		/* quantification cubes for preimage */
    DdNode **nscube;		/* next state variables in each part */
    DdNode *preiabs;		/* present state vars and inputs in no part */
    DdNode *prepabs;		/* inputs in no part */
    DdNode *xw;			/* cube of all present states and PIs */
    NtrHeap *factors;		/* factors extracted from the image */
    int nlatches;		/* number of latches */
    DdNode **x;			/* array of present state variables */
    DdNode **y;			/* array of next state variables */
} NtrPartTR;

/*---------------------------------------------------------------------------*/
/* Variable declarations                                                     */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

#ifndef TRUE
#   define TRUE 1
#endif
#ifndef FALSE
#   define FALSE 0
#endif

/**Macro***********************************************************************

  Synopsis     [Returns 1 if the two arguments are identical strings.]

  Description  []

  SideEffects  [none]

  SeeAlso      []

******************************************************************************/
#define STRING_EQUAL(s1,s2) (strcmp((s1),(s2)) == 0)


/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Function prototypes                                                       */
/*---------------------------------------------------------------------------*/

extern int Ntr_buildDDs (BnetNetwork *net, DdManager *dd, NtrOptions *option, BnetNetwork *net2);
extern NtrPartTR * Ntr_buildTR (DdManager *dd, BnetNetwork *net, NtrOptions *option, int image);
extern DdNode * Ntr_TransitiveClosure (DdManager *dd, NtrPartTR *TR, NtrOptions *option);
extern int Ntr_Trav (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern int Ntr_SCC (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern int Ntr_ClosureTrav (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern void Ntr_freeTR (DdManager *dd, NtrPartTR *TR);
extern NtrPartTR * Ntr_cloneTR (NtrPartTR *TR);
extern DdNode * Ntr_initState (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern DdNode * Ntr_getStateCube (DdManager *dd, BnetNetwork *net, char *filename, int pr);
extern int Ntr_Envelope (DdManager *dd, NtrPartTR *TR, FILE *dfp, NtrOptions *option);
extern int Ntr_TestMinimization (DdManager *dd, BnetNetwork *net1, BnetNetwork *net2, NtrOptions *option);
extern int Ntr_TestDensity (DdManager *dd, BnetNetwork *net1, NtrOptions *option);
extern int Ntr_TestDecomp (DdManager *dd, BnetNetwork *net1, NtrOptions *option);
extern int Ntr_VerifyEquivalence (DdManager *dd, BnetNetwork *net1, BnetNetwork *net2, NtrOptions *option);
extern int Ntr_TestCofactorEstimate (DdManager * dd, BnetNetwork * net, NtrOptions * option);
extern int Ntr_TestClipping (DdManager *dd, BnetNetwork *net1, BnetNetwork *net2, NtrOptions *option);
extern int Ntr_TestEquivAndContain (DdManager *dd, BnetNetwork *net1, BnetNetwork *net2, NtrOptions *option);
extern int Ntr_TestClosestCube (DdManager * dd, BnetNetwork * net, NtrOptions * option);
extern int Ntr_TestTwoLiteralClauses (DdManager * dd, BnetNetwork * net1, NtrOptions * option);
extern int Ntr_TestCharToVect(DdManager * dd, BnetNetwork * net1, NtrOptions * option);
extern int Ntr_maxflow (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern double Ntr_maximum01Flow (DdManager *bdd, DdNode *sx, DdNode *ty, DdNode *E, DdNode **F, DdNode **cut, DdNode **x, DdNode **y, DdNode **z, int n, int pr);
extern int Ntr_testZDD (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern int Ntr_testISOP (DdManager *dd, BnetNetwork *net, NtrOptions *option);
extern NtrHeap * Ntr_InitHeap (int size);
extern void Ntr_FreeHeap (NtrHeap *heap);
extern int Ntr_HeapInsert (NtrHeap *heap, void *item, int key);
extern int Ntr_HeapExtractMin (NtrHeap *heap, void *item, int *key);
extern int Ntr_HeapCount (NtrHeap *heap);
extern NtrHeap * Ntr_HeapClone (NtrHeap *source);
extern int Ntr_TestHeap (NtrHeap *heap, int i);
extern int Ntr_ShortestPaths (DdManager *dd, BnetNetwork *net, NtrOptions *option);

/**AutomaticEnd***************************************************************/

#ifdef __cplusplus
}
#endif

#endif /* _NTR */
