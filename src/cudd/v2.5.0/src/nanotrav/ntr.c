/**CFile***********************************************************************

  FileName    [ntr.c]

  PackageName [ntr]

  Synopsis    [A very simple reachability analysis program.]

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

******************************************************************************/

#include "ntr.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define NTR_MAX_DEP_SIZE 20

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
static char rcsid[] UTIL_UNUSED = "$Id: ntr.c,v 1.28 2012/02/05 01:53:01 fabio Exp fabio $";
#endif

static const char *onames[] = { "T", "R" };	/* names of functions to be dumped */
static double *signatures;		/* signatures for all variables */
static BnetNetwork *staticNet;	/* pointer to network used by qsort
				** comparison function */
static DdNode **staticPart;	/* pointer to parts used by qsort
				** comparison function */

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static DdNode * makecube (DdManager *dd, DdNode **x, int n);
static void ntrInitializeCount (BnetNetwork *net, NtrOptions *option);
static void ntrCountDFS (BnetNetwork *net, BnetNode *node);
static DdNode * ntrImage (DdManager *dd, NtrPartTR *TR, DdNode *from, NtrOptions *option);
static DdNode * ntrPreimage (DdManager *dd, NtrPartTR *T, DdNode *from);
static DdNode * ntrChooseFrom (DdManager *dd, DdNode *neW, DdNode *reached, NtrOptions *option);
static DdNode * ntrUpdateReached (DdManager *dd, DdNode *oldreached, DdNode *to);
static int ntrLatchDependencies (DdManager *dd, DdNode *reached, BnetNetwork *net, NtrOptions *option);
static NtrPartTR * ntrEliminateDependencies (DdManager *dd, NtrPartTR *TR, DdNode **states, NtrOptions *option);
static int ntrUpdateQuantificationSchedule (DdManager *dd, NtrPartTR *T);
static int ntrSignatureCompare (int * ptrX, int * ptrY);
static int ntrSignatureCompare2 (int * ptrX, int * ptrY);
static int ntrPartCompare (int * ptrX, int * ptrY);
static char ** ntrAllocMatrix (int nrows, int ncols);
static void ntrFreeMatrix (char **matrix);
static void ntrPermuteParts (DdNode **a, DdNode **b, int *comesFrom, int *goesTo, int size);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Builds DDs for a network outputs and next state
  functions.]

  Description [Builds DDs for a network outputs and next state
  functions. The method is really brain-dead, but it is very simple.
  Returns 1 in case of success; 0 otherwise. Some inputs to the network
  may be shared with another network whose DDs have already been built.
  In this case we want to share the DDs as well.]

  SideEffects [the dd fields of the network nodes are modified. Uses the
  count fields of the nodes.]

  SeeAlso     []

******************************************************************************/
int
Ntr_buildDDs(
  BnetNetwork * net /* network for which DDs are to be built */,
  DdManager * dd /* DD manager */,
  NtrOptions * option /* option structure */,
  BnetNetwork * net2 /* companion network with which inputs may be shared */)
{
    int pr = option->verb;
    int result;
    int i;
    BnetNode *node, *node2;

    /* If some inputs or present state variables are shared with
    ** another network, we initialize their BDDs from that network.
    */
    if (net2 != NULL) {
	for (i = 0; i < net->npis; i++) {
	    if (!st_lookup(net->hash,net->inputs[i],&node)) {
		return(0);
	    }
	    if (!st_lookup(net2->hash,net->inputs[i],&node2)) {
		/* This input is not shared. */
		result = Bnet_BuildNodeBDD(dd,node,net->hash,
					   option->locGlob,option->nodrop);
		if (result == 0) return(0);
	    } else {
		if (node2->dd == NULL) return(0);
		node->dd = node2->dd;
		Cudd_Ref(node->dd);
		node->var = node2->var;
		node->active = node2->active;
	    }
	}
	for (i = 0; i < net->nlatches; i++) {
	    if (!st_lookup(net->hash,net->latches[i][1],&node)) {
		return(0);
	    }
	    if (!st_lookup(net2->hash,net->latches[i][1],&node2)) {
		/* This present state variable is not shared. */
		result = Bnet_BuildNodeBDD(dd,node,net->hash,
					   option->locGlob,option->nodrop);
		if (result == 0) return(0);
	    } else {
		if (node2->dd == NULL) return(0);
		node->dd = node2->dd;
		Cudd_Ref(node->dd);
		node->var = node2->var;
		node->active = node2->active;
	    }
	}
    } else {
	/* First assign variables to inputs if the order is provided.
	** (Either in the .blif file or in an order file.)
	*/
	if (option->ordering == PI_PS_FROM_FILE) {
	    /* Follow order given in input file. First primary inputs
	    ** and then present state variables.
	    */
	    for (i = 0; i < net->npis; i++) {
		if (!st_lookup(net->hash,net->inputs[i],&node)) {
		    return(0);
		}
		result = Bnet_BuildNodeBDD(dd,node,net->hash,
					   option->locGlob,option->nodrop);
		if (result == 0) return(0);
	    }
	    for (i = 0; i < net->nlatches; i++) {
		if (!st_lookup(net->hash,net->latches[i][1],&node)) {
		    return(0);
		}
		result = Bnet_BuildNodeBDD(dd,node,net->hash,
					   option->locGlob,option->nodrop);
		if (result == 0) return(0);
	    }
	} else if (option->ordering == PI_PS_GIVEN) {
	    result = Bnet_ReadOrder(dd,option->orderPiPs,net,option->locGlob,
				    option->nodrop);
	    if (result == 0) return(0);
	} else {
	    result = Bnet_DfsVariableOrder(dd,net);
	    if (result == 0) return(0);
	}
    }
    /* At this point the BDDs of all primary inputs and present state
    ** variables have been built. */

    /* Currently noBuild doesn't do much. */
    if (option->noBuild == TRUE)
	return(1);

    if (option->locGlob == BNET_LOCAL_DD) {
	node = net->nodes;
	while (node != NULL) {
	    result = Bnet_BuildNodeBDD(dd,node,net->hash,BNET_LOCAL_DD,TRUE);
	    if (result == 0) {
		return(0);
	    }
	    if (pr > 2) {
		(void) fprintf(stdout,"%s",node->name);
		Cudd_PrintDebug(dd,node->dd,Cudd_ReadSize(dd),pr);
	    }
	    node = node->next;
	}
    } else { /* option->locGlob == BNET_GLOBAL_DD */
	/* Create BDDs with DFS from the primary outputs and the next
	** state functions. If the inputs had not been ordered yet,
	** this would result in a DFS order for the variables.
	*/

	ntrInitializeCount(net,option);

	if (option->node != NULL &&
	    option->closestCube == FALSE && option->dontcares == FALSE) {
	    if (!st_lookup(net->hash,option->node,&node)) {
		return(0);
	    }
	    result = Bnet_BuildNodeBDD(dd,node,net->hash,BNET_GLOBAL_DD,
				       option->nodrop);
	    if (result == 0) return(0);
	} else {
	    if (option->stateOnly == FALSE) {
		for (i = 0; i < net->npos; i++) {
		    if (!st_lookup(net->hash,net->outputs[i],&node)) {
			continue;
		    }
		    result = Bnet_BuildNodeBDD(dd,node,net->hash,
					       BNET_GLOBAL_DD,option->nodrop);
		    if (result == 0) return(0);
		    if (option->progress)  {
			(void) fprintf(stdout,"%s\n",node->name);
		    }
#if 0
		    Cudd_PrintDebug(dd,node->dd,net->ninputs,option->verb);
#endif
		}
	    }
	    for (i = 0; i < net->nlatches; i++) {
		if (!st_lookup(net->hash,net->latches[i][0],&node)) {
		    continue;
		}
		result = Bnet_BuildNodeBDD(dd,node,net->hash,BNET_GLOBAL_DD,
					   option->nodrop);
		if (result == 0) return(0);
		if (option->progress)  {
		    (void) fprintf(stdout,"%s\n",node->name);
		}
#if 0
		Cudd_PrintDebug(dd,node->dd,net->ninputs,option->verb);
#endif
	    }
	}
	/* Make sure all inputs have a DD and dereference the DDs of
	** the nodes that are not reachable from the outputs.
	*/
	for (i = 0; i < net->npis; i++) {
	    if (!st_lookup(net->hash,net->inputs[i],&node)) {
		return(0);
	    }
	    result = Bnet_BuildNodeBDD(dd,node,net->hash,BNET_GLOBAL_DD,
				       option->nodrop);
	    if (result == 0) return(0);
	    if (node->count == -1) Cudd_RecursiveDeref(dd,node->dd);
	}
	for (i = 0; i < net->nlatches; i++) {
	    if (!st_lookup(net->hash,net->latches[i][1],&node)) {
		return(0);
	    }
	    result = Bnet_BuildNodeBDD(dd,node,net->hash,BNET_GLOBAL_DD,
				       option->nodrop);
	    if (result == 0) return(0);
	    if (node->count == -1) Cudd_RecursiveDeref(dd,node->dd);
	}

	/* Dispose of the BDDs of the internal nodes if they have not
	** been dropped already.
	*/
	if (option->nodrop == TRUE) {
	    for (node = net->nodes; node != NULL; node = node->next) {
		if (node->dd != NULL && node->count != -1 &&
		    (node->type == BNET_INTERNAL_NODE ||
		    node->type == BNET_INPUT_NODE ||
		    node->type == BNET_PRESENT_STATE_NODE)) {
		    Cudd_RecursiveDeref(dd,node->dd);
		    if (node->type == BNET_INTERNAL_NODE) node->dd = NULL;
		}
	    }
	}
    }

    return(1);

} /* end of buildDD */


/**Function********************************************************************

  Synopsis    [Builds the transition relation for a network.]

  Description [Builds the transition relation for a network. Returns a
  pointer to the transition relation structure if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
NtrPartTR *
Ntr_buildTR(
  DdManager * dd /* manager */,
  BnetNetwork * net /* network */,
  NtrOptions * option /* options */,
  int  image /* image type: monolithic ... */)
{
    NtrPartTR *TR;
    DdNode *T, *delta, *support, *scan, *tmp, *preiabs, *prepabs;
    DdNode **part, **absicubes, **abspcubes, **nscube, *mnscube;
    DdNode **x, **y;
    DdNode **pi;
    int i;
    int xlevel;
    BnetNode *node;
    int *schedule;
    int depth = 0;

    /* Initialize transition relation structure. */
    TR = ALLOC(NtrPartTR,1);
    if (TR == NULL) goto endgame;
    TR->nlatches = net->nlatches;
    if (image == NTR_IMAGE_MONO) {
	TR->nparts = 1;
    } else if (image == NTR_IMAGE_PART || image == NTR_IMAGE_CLIP ||
	       image == NTR_IMAGE_DEPEND) {
	TR->nparts = net->nlatches;
    } else {
	(void) fprintf(stderr,"Unrecognized image method (%d). Using part.\n",
		       image);
	TR->nparts = net->nlatches;
    }
    TR->factors = Ntr_InitHeap(TR->nlatches);
    if (TR->factors == NULL) goto endgame;
    /* Allocate arrays for present state and next state variables. */
    TR->x = x = ALLOC(DdNode *,TR->nlatches);
    if (x == NULL) goto endgame;
    TR->y = y = ALLOC(DdNode *,TR->nlatches);
    if (y == NULL) goto endgame;
    /* Allocate array for primary input variables. */
    pi = ALLOC(DdNode *,net->npis);
    if (pi == NULL) goto endgame;
    /* Allocate array for partitioned transition relation. */
    part = ALLOC(DdNode *,net->nlatches);
    if (part == NULL) goto endgame;
    /* Allocate array of next state cubes. */
    nscube = ALLOC(DdNode *,net->nlatches);
    if (nscube == NULL) goto endgame;
    /* Allocate array for quantification schedule and initialize it. */
    schedule = ALLOC(int,Cudd_ReadSize(dd));
    if (schedule == NULL) goto endgame;
    for (i = 0; i < Cudd_ReadSize(dd); i++) {
	schedule[i] = -1;
    }

    /* Create partitioned transition relation from network. */
    TR->xw = Cudd_ReadOne(dd);
    Cudd_Ref(TR->xw);
    for (i = 0; i < net->nlatches; i++) {
	if (!st_lookup(net->hash,net->latches[i][1],&node)) {
	    goto endgame;
	}
	x[i] = node->dd;
	Cudd_Ref(x[i]);
	/* Add present state variable to cube TR->xw. */
	tmp = Cudd_bddAnd(dd,TR->xw,x[i]);
	if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,TR->xw);
	TR->xw = tmp;
	/* Create new y variable immediately above the x variable. */
	xlevel = Cudd_ReadPerm(dd,x[i]->index);
	y[i] = Cudd_bddNewVarAtLevel(dd,xlevel);
	Cudd_Ref(y[i]);
	/* Initialize cube of next state variables for this part. */
	nscube[i] = y[i];
	Cudd_Ref(nscube[i]);
	/* Group present and next state variable if so requested. */
	if (option->groupnsps != NTR_GROUP_NONE) {
	    int method = option->groupnsps == NTR_GROUP_DEFAULT ?
		MTR_DEFAULT : MTR_FIXED;
	    if (Cudd_MakeTreeNode(dd,y[i]->index,2,method) == NULL)
		goto endgame;
	}
	/* Get next state function and create transition relation part. */
	if (!st_lookup(net->hash,net->latches[i][0],&node)) {
	    goto endgame;
	}
	delta = node->dd;
	if (image != NTR_IMAGE_DEPEND) {
	    part[i] = Cudd_bddXnor(dd,delta,y[i]);
	    if (part[i] == NULL) goto endgame;
	} else {
	    part[i] = delta;
	}
	Cudd_Ref(part[i]);
	/* Collect scheduling info for this delta. At the end of this loop
	** schedule[i] == j means that the variable of index i does not
	** appear in any part with index greater than j, unless j == -1,
	** in which case the variable appears in no part.
	*/
	support = Cudd_Support(dd,delta);
	Cudd_Ref(support);
	scan = support;
	while (!Cudd_IsConstant(scan)) {
	    schedule[scan->index] = i;
	    scan = Cudd_T(scan);
	}
	Cudd_RecursiveDeref(dd,support);
    }

    /* Collect primary inputs. */
    for (i = 0; i < net->npis; i++) {
	if (!st_lookup(net->hash,net->inputs[i],&node)) {
	    goto endgame;
	}
	pi[i] = node->dd;
	tmp  = Cudd_bddAnd(dd,TR->xw,pi[i]);
	if (tmp == NULL) goto endgame; Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,TR->xw);
	TR->xw = tmp;
    }

    /* Build abstraction cubes. First primary input variables that go
    ** in the abstraction cubes for both monolithic and partitioned
    ** transition relations. */
    absicubes = ALLOC(DdNode *, net->nlatches);
    if (absicubes == NULL) goto endgame;
    abspcubes = ALLOC(DdNode *, net->nlatches);
    if (abspcubes == NULL) goto endgame;

    for (i = 0; i < net->nlatches; i++) {
	absicubes[i] = Cudd_ReadOne(dd);
	Cudd_Ref(absicubes[i]);
    }
    preiabs = Cudd_ReadOne(dd);
    Cudd_Ref(preiabs);

    for (i = 0; i < net->npis; i++) {
	int j = pi[i]->index;
	int k = schedule[j];
	if (k >= 0) {
	    tmp = Cudd_bddAnd(dd,absicubes[k],pi[i]);
	    if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,absicubes[k]);
	    absicubes[k] = tmp;
	} else {
	    tmp = Cudd_bddAnd(dd,preiabs,pi[i]);
	    if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,preiabs);
	    preiabs = tmp;
	}
    }
    FREE(pi);

    /* Build preimage abstraction cubes from image abstraction cubes. */
    for (i = 0; i < net->nlatches; i++) {
	abspcubes[i] = Cudd_bddAnd(dd,absicubes[i],nscube[i]);
	if (abspcubes[i] == NULL) return(NULL);
	Cudd_Ref(abspcubes[i]);
    }
    Cudd_Ref(prepabs = preiabs);

    /* For partitioned transition relations we add present state variables
    ** to the image abstraction cubes. */
    if (image != NTR_IMAGE_MONO) {
	for (i = 0; i < net->nlatches; i++) {
	    int j = x[i]->index;
	    int k = schedule[j];
	    if (k >= 0) {
		tmp = Cudd_bddAnd(dd,absicubes[k],x[i]);
		if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
		Cudd_RecursiveDeref(dd,absicubes[k]);
		absicubes[k] = tmp;
	    } else {
		tmp = Cudd_bddAnd(dd,preiabs,x[i]);
		if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
		Cudd_RecursiveDeref(dd,preiabs);
		preiabs = tmp;
	    }
	}
    }
    FREE(schedule);

    if (image != NTR_IMAGE_MONO) {
	TR->part = part;
	TR->icube = absicubes;
	TR->pcube = abspcubes;
	TR->nscube = nscube;
	TR->preiabs = preiabs;
	TR->prepabs = prepabs;
	return(TR);
    }

    /* Here we are building a monolithic TR. */

    /* Reinitialize the cube of variables to be quantified before
    ** image computation. */
    Cudd_RecursiveDeref(dd,preiabs);
    preiabs = Cudd_ReadOne(dd);
    Cudd_Ref(preiabs);

    if (option->imageClip != 1.0) {
	depth = (int) ((double) Cudd_ReadSize(dd) * option->imageClip);
    }

    /* Collapse transition relation. */
    T = Cudd_ReadOne(dd);
    Cudd_Ref(T);
    mnscube = Cudd_ReadOne(dd);
    Cudd_Ref(mnscube);
    for (i = 0; i < net->nlatches; i++) {
	/* Eliminate the primary inputs that do not appear in other parts. */
	if (depth != 0) {
	    tmp = Cudd_bddClippingAndAbstract(dd,T,part[i],absicubes[i],
					      depth,option->approx);
	} else {
	    tmp = Cudd_bddAndAbstract(dd,T,part[i],absicubes[i]);
	}
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,T);
	Cudd_RecursiveDeref(dd,part[i]);
	Cudd_RecursiveDeref(dd,absicubes[i]);
	Cudd_RecursiveDeref(dd,abspcubes[i]);
	if (option->threshold >= 0) {
	    if (option->approx) {
		T = Cudd_RemapOverApprox(dd,tmp,2*net->nlatches,
					 option->threshold,option->quality);
	    } else {
		T = Cudd_RemapUnderApprox(dd,tmp,2*net->nlatches,
					  option->threshold,option->quality);
	    }
	} else {
	    T = tmp;
	}
	if (T == NULL) return(NULL);
	Cudd_Ref(T);
	Cudd_RecursiveDeref(dd,tmp);
	/* Add the next state variables of this part to the cube of all
	** next state variables. */
	tmp = Cudd_bddAnd(dd,mnscube,nscube[i]);
	if (tmp == NULL) return(NULL);
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,mnscube);
	mnscube = tmp;
	Cudd_RecursiveDeref(dd,nscube[i]);
	(void) printf("@"); fflush(stdout);
    }
    (void) printf("\n");
#if 0
    (void) printf("T"); Cudd_PrintDebug(dd,T,2*net->nlatches,2);
#endif

    /* Clean up. */
    FREE(absicubes);
    FREE(abspcubes);
    FREE(part);
    FREE(nscube);

    TR->part = part = ALLOC(DdNode *,1);
    if (part == NULL) goto endgame;
    part[0] = T;

    /* Build cube of x (present state) variables for abstraction. */
    TR->icube = absicubes = ALLOC(DdNode *,1);
    if (absicubes == NULL) goto endgame;
    absicubes[0] = makecube(dd,x,TR->nlatches);
    if (absicubes[0] == NULL) return(0);
    Cudd_Ref(absicubes[0]);
    /* Build cube of y (next state) variables for abstraction. */
    TR->pcube = abspcubes = ALLOC(DdNode *,1);
    if (abspcubes == NULL) goto endgame;
    abspcubes[0] = makecube(dd,y,TR->nlatches);
    if (abspcubes[0] == NULL) return(0);
    Cudd_Ref(abspcubes[0]);
    TR->preiabs = preiabs;
    TR->prepabs = prepabs;

    TR->nscube = ALLOC(DdNode *,1);
    if (TR->nscube == NULL) return(NULL);
    TR->nscube[0] = mnscube;

    return(TR);

endgame:

    return(NULL);

} /* end of Ntr_buildTR */


/**Function********************************************************************

  Synopsis    [Frees the transition relation for a network.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
void
Ntr_freeTR(
  DdManager * dd,
  NtrPartTR * TR)
{
    int i;
    for (i = 0; i < TR->nlatches; i++) {
	Cudd_RecursiveDeref(dd,TR->x[i]);
	Cudd_RecursiveDeref(dd,TR->y[i]);
    }
    FREE(TR->x);
    FREE(TR->y);
    for (i = 0; i < TR->nparts; i++) {
	Cudd_RecursiveDeref(dd,TR->part[i]);
	Cudd_RecursiveDeref(dd,TR->icube[i]);
	Cudd_RecursiveDeref(dd,TR->pcube[i]);
	Cudd_RecursiveDeref(dd,TR->nscube[i]);
    }
    FREE(TR->part);
    FREE(TR->icube);
    FREE(TR->pcube);
    FREE(TR->nscube);
    Cudd_RecursiveDeref(dd,TR->preiabs);
    Cudd_RecursiveDeref(dd,TR->prepabs);
    Cudd_RecursiveDeref(dd,TR->xw);
    for (i = 0; i < TR->factors->nslots; i++) {
	Cudd_RecursiveDeref(dd, (DdNode *) TR->factors->slots[i].item);
    }
    Ntr_FreeHeap(TR->factors);
    FREE(TR);

    return;

} /* end of Ntr_freeTR */


/**Function********************************************************************

  Synopsis    [Makes a copy of a transition relation.]

  Description [Makes a copy of a transition relation. Returns a pointer
  to the copy if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_buildTR Ntr_freeTR]

******************************************************************************/
NtrPartTR *
Ntr_cloneTR(
  NtrPartTR *TR)
{
    NtrPartTR *T;
    int nparts, nlatches, i;

    T = ALLOC(NtrPartTR,1);
    if (T == NULL) return(NULL);
    nparts = T->nparts = TR->nparts;
    nlatches = T->nlatches = TR->nlatches;
    T->part = ALLOC(DdNode *,nparts);
    if (T->part == NULL) {
	FREE(T);
	return(NULL);
    }
    T->icube = ALLOC(DdNode *,nparts);
    if (T->icube == NULL) {
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    T->pcube = ALLOC(DdNode *,nparts);
    if (T->pcube == NULL) {
	FREE(T->icube);
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    T->x = ALLOC(DdNode *,nlatches);
    if (T->x == NULL) {
	FREE(T->pcube);
	FREE(T->icube);
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    T->y = ALLOC(DdNode *,nlatches);
    if (T->y == NULL) {
	FREE(T->x);
	FREE(T->pcube);
	FREE(T->icube);
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    T->nscube = ALLOC(DdNode *,nparts);
    if (T->nscube == NULL) {
	FREE(T->y);
	FREE(T->x);
	FREE(T->pcube);
	FREE(T->icube);
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    T->factors = Ntr_HeapClone(TR->factors);
    if (T->factors == NULL) {
	FREE(T->nscube);
	FREE(T->y);
	FREE(T->x);
	FREE(T->pcube);
	FREE(T->icube);
	FREE(T->part);
	FREE(T);
	return(NULL);
    }
    for (i = 0; i < T->factors->nslots; i++) {
	Cudd_Ref((DdNode *) T->factors->slots[i].item);
    }
    for (i = 0; i < nparts; i++) {
	T->part[i] = TR->part[i];
	Cudd_Ref(T->part[i]);
	T->icube[i] = TR->icube[i];
	Cudd_Ref(T->icube[i]);
	T->pcube[i] = TR->pcube[i];
	Cudd_Ref(T->pcube[i]);
	T->nscube[i] = TR->nscube[i];
	Cudd_Ref(T->nscube[i]);
    }
    T->preiabs = TR->preiabs;
    Cudd_Ref(T->preiabs);
    T->prepabs = TR->prepabs;
    Cudd_Ref(T->prepabs);
    T->xw = TR->xw;
    Cudd_Ref(T->xw);
    for (i = 0; i < nlatches; i++) {
	T->x[i] = TR->x[i];
	Cudd_Ref(T->x[i]);
	T->y[i] = TR->y[i];
	Cudd_Ref(T->y[i]);
    }

    return(T);

} /* end of Ntr_cloneTR */


/**Function********************************************************************

  Synopsis    [Poor man's traversal procedure.]

  Description [Poor man's traversal procedure. based on the monolithic
  transition relation.  Returns 1 in case of success; 0 otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_ClosureTrav]

******************************************************************************/
int
Ntr_Trav(
  DdManager * dd /* DD manager */,
  BnetNetwork * net /* network */,
  NtrOptions * option /* options */)
{
    NtrPartTR *TR;		/* Transition relation */
    DdNode *init;		/* initial state(s) */
    DdNode *from;
    DdNode *to;
    DdNode *reached;
    DdNode *neW;
    DdNode *one, *zero;
    int depth;
    int retval;
    int pr = option->verb;
    int initReord = Cudd_ReadReorderings(dd);

    if (option->traverse == FALSE || net->nlatches == 0) return(1);
    (void) printf("Building transition relation. Time = %s\n",
		  util_print_time(util_cpu_time() - option->initialTime));
    one = Cudd_ReadOne(dd);
    zero = Cudd_Not(one);

    /* Build transition relation and initial states. */
    TR = Ntr_buildTR(dd,net,option,option->image);
    if (TR == NULL) return(0);
    retval = Cudd_SetVarMap(dd,TR->x,TR->y,TR->nlatches);
    (void) printf("Transition relation: %d parts %d latches %d nodes\n",
		  TR->nparts, TR->nlatches,
		  Cudd_SharingSize(TR->part, TR->nparts));
    (void) printf("Traversing. Time = %s\n",
		  util_print_time(util_cpu_time() - option->initialTime));
    init = Ntr_initState(dd,net,option);
    if (init == NULL) return(0);

    /* Initialize From. */
    Cudd_Ref(from = init);
    (void) printf("S0"); Cudd_PrintDebug(dd,from,TR->nlatches,pr);

    /* Initialize Reached. */
    Cudd_Ref(reached = from);

    /* Start traversal. */
    for (depth = 0; ; depth++) {
	/* Image computation. */
	to = ntrImage(dd,TR,from,option);
	if (to == NULL) {
	    Cudd_RecursiveDeref(dd,reached);
	    Cudd_RecursiveDeref(dd,from);
	    return(0);
	}
	Cudd_RecursiveDeref(dd,from);

	/* Find new states. */
	neW = Cudd_bddAnd(dd,to,Cudd_Not(reached));
	if (neW == NULL) {
	    Cudd_RecursiveDeref(dd,reached);
	    Cudd_RecursiveDeref(dd,to);
	    return(0);
	}
	Cudd_Ref(neW);
	Cudd_RecursiveDeref(dd,to);

	/* Check for convergence. */
	if (neW == zero) break;

	/* Dump current reached states if requested. */
	if (option->store == depth) {
	    int ok = Dddmp_cuddBddStore(dd, NULL, reached, NULL,
					NULL, DDDMP_MODE_TEXT, DDDMP_VARIDS,
					option->storefile, NULL);
	    if (ok == 0) return(0);
	    (void) printf("Storing reached in %s after %i iterations.\n",
			  option->storefile, depth);
	    break;
	}

	/* Update reached. */
	reached = ntrUpdateReached(dd,reached,neW);
	if (reached == NULL) {
	    Cudd_RecursiveDeref(dd,neW);
	    return(0);
	}

	/* Prepare for new iteration. */
	from = ntrChooseFrom(dd,neW,reached,option);
	if (from == NULL) {
	    Cudd_RecursiveDeref(dd,reached);
	    Cudd_RecursiveDeref(dd,neW);
	    return(0);
	}
	Cudd_RecursiveDeref(dd,neW);
	(void) printf("From[%d]",depth+1);
	Cudd_PrintDebug(dd,from,TR->nlatches,pr);
	(void) printf("Reached[%d]",depth+1);
	Cudd_PrintDebug(dd,reached,TR->nlatches,pr);
	if (pr > 0) {
	    if (!Cudd_ApaPrintMinterm(stdout, dd, reached, TR->nlatches))
		return(0);
	    if (!Cudd_ApaPrintMintermExp(stdout, dd, reached, TR->nlatches, 6))
		return(0);
	} else {
	    (void) printf("\n");
	}
    }

    /* Print out result. */
    (void) printf("depth = %d\n", depth);
    (void) printf("R"); Cudd_PrintDebug(dd,reached,TR->nlatches,pr);

    /* Dump to file if requested. */
    if (option->bdddump) {
	DdNode *dfunc[2];	/* addresses of the functions to be dumped */
	char *onames[2];	/* names of the functions to be dumped */
	dfunc[0] = TR->part[0];		onames[0] = (char *) "T";
	dfunc[1] = reached;		onames[1] = (char *) "R";
	retval = Bnet_bddArrayDump(dd, net, option->dumpfile, dfunc,
				   onames, 2, option->dumpFmt);
	if (retval == 0) return(0);
    }

    if (option->depend) {
	retval = ntrLatchDependencies(dd, reached, net, option);
	if (retval == -1) return(0);
	(void) printf("%d latches are redundant\n", retval);
    }
    /* Clean up. */
    Cudd_RecursiveDeref(dd,reached);
    Cudd_RecursiveDeref(dd,neW);
    Cudd_RecursiveDeref(dd,init);
    Ntr_freeTR(dd,TR);

    if (Cudd_ReadReorderings(dd) > initReord) {
	(void) printf("Order at the end of reachability analysis\n");
	retval = Bnet_PrintOrder(net,dd);
	if (retval == 0) return(0);
    }
    return(1);

} /* end of Ntr_Trav */


/**Function********************************************************************

  Synopsis    [Computes the SCCs of the STG.]

  Description [Computes the strongly connected components of the state
  transition graph.  Only the first 10 SCCs are computed. Returns 1 in
  case of success; 0 otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_Trav]

******************************************************************************/
int
Ntr_SCC(
  DdManager * dd /* DD manager */,
  BnetNetwork * net /* network */,
  NtrOptions * option /* options */)
{
    NtrPartTR *TR;		/* Transition relation */
    DdNode *init;		/* initial state(s) */
    DdNode *from;
    DdNode *to;
    DdNode *reached, *reaching;
    DdNode *neW;
    DdNode *one, *zero;
    DdNode *states, *scc;
    DdNode *tmp;
    DdNode *SCCs[10];
    int depth;
    int nscc = 0;
    int retval;
    int pr = option->verb;
    int i;

    if (option->scc == FALSE || net->nlatches == 0) return(1);
    (void) printf("Building transition relation. Time = %s\n",
		  util_print_time(util_cpu_time() - option->initialTime));
    one = Cudd_ReadOne(dd);
    zero = Cudd_Not(one);

    /* Build transition relation and initial states. */
    TR = Ntr_buildTR(dd,net,option,option->image);
    if (TR == NULL) return(0);
    retval = Cudd_SetVarMap(dd,TR->x,TR->y,TR->nlatches);
    (void) printf("Transition relation: %d parts %d latches %d nodes\n",
		  TR->nparts, TR->nlatches,
		  Cudd_SharingSize(TR->part, TR->nparts));
    (void) printf("Computing SCCs. Time = %s\n",
		  util_print_time(util_cpu_time() - option->initialTime));

    /* Consider all SCCs, including those not reachable. */
    states = one;
    Cudd_Ref(states);

    while (states != zero) {
	if (nscc == 0) {
	    tmp = Ntr_initState(dd,net,option);
	    if (tmp == NULL) return(0);
	    init = Cudd_bddPickOneMinterm(dd,tmp,TR->x,TR->nlatches);
	} else {
	    init = Cudd_bddPickOneMinterm(dd,states,TR->x,TR->nlatches);
	}
	if (init == NULL) return(0);
	Cudd_Ref(init);
	if (nscc == 0) {
	    Cudd_RecursiveDeref(dd,tmp);
	}
	/* Initialize From. */
	Cudd_Ref(from = init);
	(void) printf("S0"); Cudd_PrintDebug(dd,from,TR->nlatches,pr);

	/* Initialize Reached. */
	Cudd_Ref(reached = from);

	/* Start forward traversal. */
	for (depth = 0; ; depth++) {
	    /* Image computation. */
	    to = ntrImage(dd,TR,from,option);
	    if (to == NULL) {
		return(0);
	    }
	    Cudd_RecursiveDeref(dd,from);

	    /* Find new states. */
	    tmp = Cudd_bddAnd(dd,to,states);
	    if (tmp == NULL) return(0); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,to);
	    neW = Cudd_bddAnd(dd,tmp,Cudd_Not(reached));
	    if (neW == NULL) return(0); Cudd_Ref(neW);
	    Cudd_RecursiveDeref(dd,tmp);

	    /* Check for convergence. */
	    if (neW == zero) break;

	    /* Update reached. */
	    reached = ntrUpdateReached(dd,reached,neW);
	    if (reached == NULL) {
		return(0);
	    }

	    /* Prepare for new iteration. */
	    from = ntrChooseFrom(dd,neW,reached,option);
	    if (from == NULL) {
		return(0);
	    }
	    Cudd_RecursiveDeref(dd,neW);
	    (void) printf("From[%d]",depth+1);
	    Cudd_PrintDebug(dd,from,TR->nlatches,pr);
	    (void) printf("Reached[%d]",depth+1);
	    Cudd_PrintDebug(dd,reached,TR->nlatches,pr);
	    if (pr <= 0) {
		(void) printf("\n");
	    }
	}
	Cudd_RecursiveDeref(dd,neW);

	/* Express reached in terms of y variables. This allows us to
	** efficiently test for termination during the backward traversal. */
	tmp = Cudd_bddVarMap(dd,reached);
	if (tmp == NULL) return(0);
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,reached);
	reached = tmp;

	/* Initialize from and reaching. */
	from = Cudd_bddVarMap(dd,init);
	Cudd_Ref(from);
	(void) printf("S0"); Cudd_PrintDebug(dd,from,TR->nlatches,pr);
	Cudd_Ref(reaching = from);

	/* Start backward traversal. */
	for (depth = 0; ; depth++) {
	    /* Preimage computation. */
	    to = ntrPreimage(dd,TR,from);
	    if (to == NULL) {
		return(0);
	    }
	    Cudd_RecursiveDeref(dd,from);

	    /* Find new states. */
	    tmp = Cudd_bddAnd(dd,to,reached);
	    if (tmp == NULL) return(0); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,to);
	    neW = Cudd_bddAnd(dd,tmp,Cudd_Not(reaching));
	    if (neW == NULL) return(0); Cudd_Ref(neW);
	    Cudd_RecursiveDeref(dd,tmp);

	    /* Check for convergence. */
	    if (neW == zero) break;

	    /* Update reaching. */
	    reaching = ntrUpdateReached(dd,reaching,neW);
	    if (reaching == NULL) {
		return(0);
	    }

	    /* Prepare for new iteration. */
	    from = ntrChooseFrom(dd,neW,reaching,option);
	    if (from == NULL) {
		return(0);
	    }
	    Cudd_RecursiveDeref(dd,neW);
	    (void) printf("From[%d]",depth+1);
	    Cudd_PrintDebug(dd,from,TR->nlatches,pr);
	    (void) printf("Reaching[%d]",depth+1);
	    Cudd_PrintDebug(dd,reaching,TR->nlatches,pr);
	    if (pr <= 0) {
		(void) printf("\n");
	    }
	}

	scc = Cudd_bddAnd(dd,reached,reaching);
	if (scc == NULL) {
	    return(0);
	}
	Cudd_Ref(scc);
	SCCs[nscc] = Cudd_bddVarMap(dd,scc);
	if (SCCs[nscc] == NULL) return(0);
	Cudd_Ref(SCCs[nscc]);
	Cudd_RecursiveDeref(dd,scc);
	/* Print out result. */
	(void) printf("SCC[%d]",nscc);
	Cudd_PrintDebug(dd,SCCs[nscc],TR->nlatches,pr);
	tmp = Cudd_bddAnd(dd,states,Cudd_Not(SCCs[nscc]));
	if (tmp == NULL) {
	    return(0);
	}
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,states);
	states = tmp;
	Cudd_RecursiveDeref(dd,reached);
	Cudd_RecursiveDeref(dd,reaching);
	Cudd_RecursiveDeref(dd,neW);
	Cudd_RecursiveDeref(dd,init);
	nscc++;
	if (nscc > 9) break;
    }

    if (states != zero) {
	(void) fprintf(stdout,"More than 10 SCCs. Only the first 10 are computed.\n");
    }

    /* Dump to file if requested. */
    if (option->bdddump) {
	char *sccnames[10];	/* names of the SCCs */
	sccnames[0] = (char *) "SCC0";
	sccnames[1] = (char *) "SCC1";
	sccnames[2] = (char *) "SCC2";
	sccnames[3] = (char *) "SCC3";
	sccnames[4] = (char *) "SCC4";
	sccnames[5] = (char *) "SCC5";
	sccnames[6] = (char *) "SCC6";
	sccnames[7] = (char *) "SCC7";
	sccnames[8] = (char *) "SCC8";
	sccnames[9] = (char *) "SCC9";
	retval = Bnet_bddArrayDump(dd, net, option->dumpfile, SCCs,
				   sccnames, nscc, option->dumpFmt);
	if (retval == 0) return(0);
    }

    /* Verify that the SCCs form a partition of the universe. */
    scc = zero;
    Cudd_Ref(scc);
    for (i = 0; i < nscc; i++) {
	assert(Cudd_bddLeq(dd,SCCs[i],Cudd_Not(scc)));
	tmp = Cudd_bddOr(dd,SCCs[i],scc);
	if (tmp == NULL) return(0);
	Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,scc);
	scc = tmp;
	Cudd_RecursiveDeref(dd,SCCs[i]);
    }
    assert(scc == Cudd_Not(states));

    /* Clean up. */
    Cudd_RecursiveDeref(dd,scc);
    Cudd_RecursiveDeref(dd,states);
    Ntr_freeTR(dd,TR);

    return(1);

} /* end of Ntr_SCC */


/**Function********************************************************************

  Synopsis    [Transitive closure traversal procedure.]

  Description [Traversal procedure. based on the transitive closure of the
  transition relation.  Returns 1 in case of success; 0 otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_Trav]

******************************************************************************/
int
Ntr_ClosureTrav(
  DdManager * dd /* DD manager */,
  BnetNetwork * net /* network */,
  NtrOptions * option /* options */)
{
    DdNode *init;
    DdNode *T;
    NtrPartTR *TR;
    int retval;
    int pr = option->verb;	/* verbosity level */
    DdNode *dfunc[2];		/* addresses of the functions to be dumped */
    char *onames[2];		/* names of the functions to be dumped */
    DdNode *reached, *reachedy, *reachedx;

    /* Traverse if requested and if the circuit is sequential. */
    if (option->closure == FALSE || net->nlatches == 0) return(1);

    TR = Ntr_buildTR(dd,net,option,NTR_IMAGE_MONO);
    if (TR == NULL) return(0);
    (void) printf("TR"); Cudd_PrintDebug(dd,TR->part[0],2*TR->nlatches,pr);
    T = Ntr_TransitiveClosure(dd,TR,option);
    if (T == NULL) return(0);
    Cudd_Ref(T);
    (void) printf("TC"); Cudd_PrintDebug(dd,T,2*TR->nlatches,pr);

    init = Ntr_initState(dd,net,option);
    if (init == NULL) return(0);
    (void) printf("S0"); Cudd_PrintDebug(dd,init,TR->nlatches,pr);

    /* Image computation. */
    if (option->closureClip != 1.0) {
	int depth = (int) ((double) Cudd_ReadSize(dd) * option->closureClip);
	reachedy = Cudd_bddClippingAndAbstract(dd,T,init,TR->icube[0],
					       depth,option->approx);
    } else {
	reachedy = Cudd_bddAndAbstract(dd,T,init,TR->icube[0]);
    }
    if (reachedy == NULL) return(0);
    Cudd_Ref(reachedy);

    /* Express in terms of present state variables. */
    reachedx = Cudd_bddSwapVariables(dd,reachedy,TR->x,TR->y,TR->nlatches);
    if (reachedx == NULL) return(0);
    Cudd_Ref(reachedx);
    Cudd_RecursiveDeref(dd,reachedy);

    /* Add initial state. */
    reached = Cudd_bddOr(dd,reachedx,init);
    if (reached == NULL) return(0);
    Cudd_Ref(reached);
    Cudd_RecursiveDeref(dd,reachedx);

    /* Print out result. */
    (void) printf("R"); Cudd_PrintDebug(dd,reached,TR->nlatches,pr);

    /* Dump to file if requested. */
    if (option->bdddump) {
	dfunc[0] = T;		onames[0] = (char *) "TC";
	dfunc[1] = reached;	onames[1] = (char *) "R";
	retval = Bnet_bddArrayDump(dd, net, option->dumpfile, dfunc,
				   onames, 2, option->dumpFmt);
	if (retval == 0) return(0);
    }

    /* Clean up. */
    Cudd_RecursiveDeref(dd,reached);
    Cudd_RecursiveDeref(dd,init);
    Cudd_RecursiveDeref(dd,T);
    Ntr_freeTR(dd,TR);

    return(1);

} /* end of Ntr_ClosureTrav */


/**Function********************************************************************

  Synopsis    [Builds the transitive closure of a transition relation.]

  Description [Builds the transitive closure of a transition relation.
  Returns a BDD if successful; NULL otherwise. Uses a simple squaring
  algorithm.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Ntr_TransitiveClosure(
  DdManager * dd,
  NtrPartTR * TR,
  NtrOptions * option)
{
    DdNode *T,*oldT,*Txz,*Tzy,*Tred,*square,*zcube;
    DdNode **z;
    int i;
    int depth = 0;
    int ylevel;
    int done;

    if (option->image != NTR_IMAGE_MONO) return(NULL);

    /* Create array of auxiliary variables. */
    z = ALLOC(DdNode *,TR->nlatches);
    if (z == NULL)
	return(NULL);
    for (i = 0; i < TR->nlatches; i++) {
	ylevel = Cudd_ReadIndex(dd,TR->y[i]->index);
	z[i] = Cudd_bddNewVarAtLevel(dd,ylevel);
	if (z[i] == NULL)
	    return(NULL);
    }
    /* Build cube of auxiliary variables. */
    zcube = makecube(dd,z,TR->nlatches);
    if (zcube == NULL) return(NULL);
    Cudd_Ref(zcube);

    if (option->closureClip != 1.0) {
	depth = (int) ((double) Cudd_ReadSize(dd) * option->imageClip);
    }

    T = TR->part[0];
    Cudd_Ref(T);
    for (i = 0; ; i++) {
	if (option->threshold >= 0) {
	    if (option->approx) {
		Tred = Cudd_RemapOverApprox(dd,T,TR->nlatches*2,
					    option->threshold,
					    option->quality);
	    } else {
		Tred = Cudd_RemapUnderApprox(dd,T,TR->nlatches*2,
					     option->threshold,
					     option->quality);
	    }
	} else {
	    Tred = T;
	}
	if (Tred == NULL) return(NULL);
	Cudd_Ref(Tred);
	/* Express T in terms of z and y variables. */
	Tzy = Cudd_bddSwapVariables(dd,Tred,TR->x,z,TR->nlatches);
	if (Tzy == NULL) return(NULL);
	Cudd_Ref(Tzy);
	/* Express T in terms of x and z variables. */
	Txz = Cudd_bddSwapVariables(dd,Tred,TR->y,z,TR->nlatches);
	if (Txz == NULL) return(NULL);
	Cudd_Ref(Txz);
	Cudd_RecursiveDeref(dd,Tred);
	/* Square */
	if (depth == 0) {
	    square = Cudd_bddAndAbstract(dd,Txz,Tzy,zcube);
	} else {
	    square = Cudd_bddClippingAndAbstract(dd,Txz,Tzy,zcube,depth,
						 option->approx);
	}
	if (square == NULL) return(NULL);
	Cudd_Ref(square);
	Cudd_RecursiveDeref(dd,Tzy);
	Cudd_RecursiveDeref(dd,Txz);
	oldT = T;
	T = Cudd_bddOr(dd,square,TR->part[0]);
	if (T == NULL) return(NULL);
	Cudd_Ref(T);
	Cudd_RecursiveDeref(dd,square);
	done = T == oldT;
	Cudd_RecursiveDeref(dd,oldT);
	if (done) break;
	(void) fprintf(stdout,"@"); fflush(stdout);
    }
    (void) fprintf(stdout, "\n");

    Cudd_RecursiveDeref(dd,zcube);
    Cudd_Deref(T);
    FREE(z);
    return(T);

} /* end of Ntr_TransitiveClosure */


/**Function********************************************************************

  Synopsis    [Builds the BDD of the initial state(s).]

  Description [Builds the BDD of the initial state(s).  Returns a BDD
  if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
DdNode *
Ntr_initState(
  DdManager * dd,
  BnetNetwork * net,
  NtrOptions * option)
{
    DdNode *res, *x, *w, *one;
    BnetNode *node;
    int i;

    if (option->load) {
	res = Dddmp_cuddBddLoad(dd, DDDMP_VAR_MATCHIDS, NULL, NULL, NULL,
				DDDMP_MODE_DEFAULT, option->loadfile, NULL);
    } else {
	one = Cudd_ReadOne(dd);
	Cudd_Ref(res = one);

	if (net->nlatches == 0) return(res);

	for (i = 0; i < net->nlatches; i++) {
	    if (!st_lookup(net->hash,net->latches[i][1],&node)) {
		goto endgame;
	    }
	    x = node->dd;
	    switch (net->latches[i][2][0]) {
	    case '0':
		w = Cudd_bddAnd(dd,res,Cudd_Not(x));
		break;
	    case '1':
		w = Cudd_bddAnd(dd,res,x);
		break;
	    default: /* don't care */
		w = res;
		break;
	    }

	    if (w == NULL) {
		Cudd_RecursiveDeref(dd,res);
		return(NULL);
	    }
	    Cudd_Ref(w);
	    Cudd_RecursiveDeref(dd,res);
	    res = w;
	}
    }
    return(res);

endgame:

    return(NULL);

} /* end of Ntr_initState */


/**Function********************************************************************

  Synopsis    [Reads a state cube from a file or creates a random one.]

  Description [Reads a state cube from a file or create a random one.
  Returns a pointer to the BDD of the sink nodes if successful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     []

*****************************************************************************/
DdNode *
Ntr_getStateCube(
  DdManager * dd,
  BnetNetwork * net,
  char * filename,
  int  pr)
{
    FILE *fp;
    DdNode *cube;
    DdNode *w;
    char *state;
    int i;
    int err;
    BnetNode *node;
    DdNode *x;
    char c[2];

    cube = Cudd_ReadOne(dd);
    if (net->nlatches == 0) {
	Cudd_Ref(cube);
	return(cube);
    }

    state = ALLOC(char,net->nlatches+1);
    if (state == NULL)
	return(NULL);
    state[net->nlatches] = 0;

    if (filename == NULL) {
	/* Pick one random minterm. */
	for (i = 0; i < net->nlatches; i++) {
	    state[i] = (char) ((Cudd_Random() & 0x2000) ? '1' : '0');
	}
    } else {
	if ((fp = fopen(filename,"r")) == NULL) {
	    (void) fprintf(stderr,"Unable to open %s\n",filename);
	    return(NULL);
	}

	/* Read string from file. Allow arbitrary amount of white space. */
	for (i = 0; !feof(fp); i++) {
	    err = fscanf(fp, "%1s", c);
	    state[i] = c[0];
	    if (err == EOF || i == net->nlatches - 1) {
		break;
	    } else if (err != 1 || strchr("012xX-", c[0]) == NULL ) {
		FREE(state);
		return(NULL);
	    }
	}
	err = fclose(fp);
	if (err == EOF) {
	    FREE(state);
	    return(NULL);
	}
    }

    /* Echo the chosen state(s). */
    if (pr > 0) {(void) fprintf(stdout,"%s\n", state);}

    Cudd_Ref(cube);
    for (i = 0; i < net->nlatches; i++) {
	if (!st_lookup(net->hash,net->latches[i][1],&node)) {
	    Cudd_RecursiveDeref(dd,cube);
	    FREE(state);
	    return(NULL);
	}
	x = node->dd;
	switch (state[i]) {
	case '0':
	    w = Cudd_bddAnd(dd,cube,Cudd_Not(x));
	    break;
	case '1':
	    w = Cudd_bddAnd(dd,cube,x);
	    break;
	default: /* don't care */
	    w = cube;
	    break;
	}

	if (w == NULL) {
	    Cudd_RecursiveDeref(dd,cube);
	    FREE(state);
	    return(NULL);
	}
	Cudd_Ref(w);
	Cudd_RecursiveDeref(dd,cube);
	cube = w;
    }

    FREE(state);
    return(cube);

} /* end of Ntr_getStateCube */


/**Function********************************************************************

  Synopsis    [Poor man's outer envelope computation.]

  Description [ Poor man's outer envelope computation based on the
  monolithic transition relation. Returns 1 in case of success; 0
  otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Ntr_Envelope(
  DdManager * dd /* DD manager */,
  NtrPartTR * TR /* transition relation */,
  FILE * dfp /* pointer to file for DD dump */,
  NtrOptions * option /* program options */)
{
    DdNode **x;	/* array of x variables */
    DdNode **y;	/* array of y variables */
    int ns;	/* number of x and y variables */
    DdNode *dfunc[2];	/* addresses of the functions to be dumped */
    DdNode *envelope, *oldEnvelope;
    DdNode *one;
    int depth;
    int retval;
    int pr = option->verb;
    int dumpFmt = option->dumpFmt;

    x = TR->x;
    y = TR->y;
    ns = TR->nlatches;

    one = Cudd_ReadOne(dd);
    retval = Cudd_SetVarMap(dd,x,y,ns);

    /* Initialize From. */
    envelope = one;
    if (envelope == NULL) return(0);
    Cudd_Ref(envelope);
    (void) printf("S0"); Cudd_PrintDebug(dd,envelope,ns,pr);

    /* Start traversal. */
    for (depth = 0; ; depth++) {
	oldEnvelope = envelope;
	/* Image computation. */
	envelope = ntrImage(dd,TR,oldEnvelope,option);
	if (envelope == NULL) {
	    Cudd_RecursiveDeref(dd,oldEnvelope);
	    return(0);
	}

	/* Check for convergence. */
	if (envelope == oldEnvelope) break;

	/* Prepare for new iteration. */
	Cudd_RecursiveDeref(dd,oldEnvelope);
	(void) fprintf(stdout,"Envelope[%d]%s",depth+1,(pr>0)? "" : "\n");
	Cudd_PrintDebug(dd,envelope,ns,pr);

    }
    /* Clean up. */
    Cudd_RecursiveDeref(dd,oldEnvelope);

    /* Print out result. */
    (void) printf("depth = %d\n", depth);
    (void) printf("Envelope"); Cudd_PrintDebug(dd,envelope,ns,pr);

    /* Write dump file if requested. */
    if (dfp != NULL) {
	dfunc[0] = TR->part[0];
	dfunc[1] = envelope;
	if (dumpFmt == 1) {
	    retval = Cudd_DumpBlif(dd,2,dfunc,NULL,(char **)onames,NULL,dfp,0);
	} else if (dumpFmt == 2) {
	    retval = Cudd_DumpDaVinci(dd,2,dfunc,NULL,(char **)onames,dfp);
	} else if (dumpFmt == 3) {
	    retval = Cudd_DumpDDcal(dd,2,dfunc,NULL,(char **)onames,dfp);
	} else if (dumpFmt == 4) {
	    retval = Cudd_DumpFactoredForm(dd,2,dfunc,NULL,
					   (char **)onames,dfp);
	} else if (dumpFmt == 5) {
	    retval = Cudd_DumpBlif(dd,2,dfunc,NULL,(char **)onames,NULL,dfp,1);
	} else {
	    retval = Cudd_DumpDot(dd,2,dfunc,NULL,(char **)onames,dfp);
	}
	if (retval != 1) {
	    (void) fprintf(stderr,"abnormal termination\n");
	    return(0);
	}
	fclose(dfp);
    }

    /* Clean up. */
    Cudd_RecursiveDeref(dd,envelope);

    return(1);

} /* end of Ntr_Envelope */


/**Function********************************************************************

  Synopsis    [Maximum 0-1 flow between source and sink states.]

  Description [Maximum 0-1 flow between source and sink
  states. Returns 1 in case of success; 0 otherwise.]

  SideEffects [Creates two new sets of variables.]

  SeeAlso     []

******************************************************************************/
int
Ntr_maxflow(
  DdManager * dd,
  BnetNetwork * net,
  NtrOptions * option)
{
    DdNode **x = NULL;
    DdNode **y = NULL;
    DdNode **z = NULL;
    DdNode *E = NULL;
    DdNode *F = NULL;
    DdNode *cut = NULL;
    DdNode *sx = NULL;
    DdNode *ty = NULL;
    DdNode *tx = NULL;
    int n;
    int pr;
    int ylevel;
    int i;
    double flow;
    int result = 0;
    NtrPartTR *TR;

    n = net->nlatches;
    pr = option->verb;
    TR = Ntr_buildTR(dd,net,option,NTR_IMAGE_MONO);
    if (TR == NULL)
	goto endgame;
    E = TR->part[0];
    x = TR->x;
    y = TR->y;
    /* Create array of auxiliary variables. */
    z = ALLOC(DdNode *,n);
    if (z == NULL)
	goto endgame;
    for (i = 0; i < n; i++) {
	ylevel = Cudd_ReadIndex(dd,y[i]->index);
	z[i] = Cudd_bddNewVarAtLevel(dd,ylevel);
	if (z[i] == NULL)
	    goto endgame;
	Cudd_Ref(z[i]);
    }
    /* Create BDDs for source and sink. */
    sx = Ntr_initState(dd,net,option);
    if (sx == NULL)
	goto endgame;
    if (pr > 0) (void) fprintf(stdout, "Sink(s): ");
    tx = Ntr_getStateCube(dd,net,option->sinkfile,pr);
    if (tx == NULL)
	goto endgame;
    ty = Cudd_bddSwapVariables(dd,tx,x,y,n);
    if (ty == NULL)
	goto endgame;
    Cudd_Ref(ty);
    Cudd_RecursiveDeref(dd,tx);
    tx = NULL;

    flow = Ntr_maximum01Flow(dd, sx, ty, E, &F, &cut, x, y, z, n, pr);
    if (flow >= 0.0)
	result = 1;
    if (pr >= 0) {
	(void) fprintf(stdout,"Maximum flow = %g\n", flow);
	(void) fprintf(stdout,"E"); Cudd_PrintDebug(dd,E,2*n,pr);
	(void) fprintf(stdout,"F"); Cudd_PrintDebug(dd,F,2*n,pr);
	(void) fprintf(stdout,"cut"); Cudd_PrintDebug(dd,cut,2*n,pr);
    }
endgame:
    /* Clean up. */
    if (TR != NULL) Ntr_freeTR(dd,TR);
    for (i = 0; i < n; i++) {
	if (z != NULL && z[i] != NULL) Cudd_RecursiveDeref(dd,z[i]);
    }
    if (z != NULL) FREE(z);
    if (F != NULL) Cudd_RecursiveDeref(dd,F);
    if (cut != NULL) Cudd_RecursiveDeref(dd,cut);
    if (sx != NULL) Cudd_RecursiveDeref(dd,sx);
    if (ty != NULL) Cudd_RecursiveDeref(dd,ty);
    return(result);

} /* end of Ntr_Maxflow */

/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Builds a positive cube of all the variables in x.]

  Description [Builds a positive cube of all the variables in x. Returns
  a BDD for the cube if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static DdNode *
makecube(
  DdManager * dd,
  DdNode ** x,
  int  n)
{
    DdNode *res, *w, *one;
    int i;

    one = Cudd_ReadOne(dd);
    Cudd_Ref(res = one);

    for (i = n-1; i >= 0; i--) {
	w = Cudd_bddAnd(dd,res,x[i]);
	if (w == NULL) {
	    Cudd_RecursiveDeref(dd,res);
	    return(NULL);
	}
	Cudd_Ref(w);
	Cudd_RecursiveDeref(dd,res);
	res = w;
    }
    Cudd_Deref(res);
    return(res);

} /* end of makecube */


/**Function********************************************************************

  Synopsis    [Initializes the count fields used to drop DDs.]

  Description [Initializes the count fields used to drop DDs.
  Before actually building the BDDs, we perform a DFS from the outputs
  to initialize the count fields of the nodes.  The initial value of the
  count field will normally coincide with the fanout of the node.
  However, if there are nodes with no path to any primary output or next
  state variable, then the initial value of count for some nodes will be
  less than the fanout. For primary outputs and next state functions we
  add 1, so that we will never try to free their DDs. The count fields
  of the nodes that are not reachable from the outputs are set to -1.]

  SideEffects [Changes the count fields of the network nodes. Uses the
  visited fields.]

  SeeAlso     []

******************************************************************************/
static void
ntrInitializeCount(
  BnetNetwork * net,
  NtrOptions * option)
{
    BnetNode *node;
    int i;

    if (option->node != NULL &&
	option->closestCube == FALSE && option->dontcares == FALSE) {
	if (!st_lookup(net->hash,option->node,&node)) {
	    (void) fprintf(stdout, "Warning: node %s not found!\n",
			   option->node);
	} else {
	    ntrCountDFS(net,node);
	    node->count++;
	}
    } else {
	if (option->stateOnly == FALSE) {
	    for (i = 0; i < net->npos; i++) {
		if (!st_lookup(net->hash,net->outputs[i],&node)) {
		    (void) fprintf(stdout,
				   "Warning: output %s is not driven!\n",
				   net->outputs[i]);
		    continue;
		}
		ntrCountDFS(net,node);
		node->count++;
	    }
	}
	for (i = 0; i < net->nlatches; i++) {
	    if (!st_lookup(net->hash,net->latches[i][0],&node)) {
		(void) fprintf(stdout,
			       "Warning: latch input %s is not driven!\n",
			       net->outputs[i]);
		continue;
	    }
	    ntrCountDFS(net,node);
	    node->count++;
	}
    }

    /* Clear visited flags. */
    node = net->nodes;
    while (node != NULL) {
	if (node->visited == 0) {
	    node->count = -1;
	} else {
	    node->visited = 0;
	}
	node = node->next;
    }

} /* end of ntrInitializeCount */


/**Function********************************************************************

  Synopsis    [Does a DFS from a node setting the count field.]

  Description []

  SideEffects [Changes the count and visited fields of the nodes it
  visits.]

  SeeAlso     [ntrLevelDFS]

******************************************************************************/
static void
ntrCountDFS(
  BnetNetwork * net,
  BnetNode * node)
{
    int i;
    BnetNode *auxnd;

    node->count++;

    if (node->visited == 1) {
	return;
    }

    node->visited = 1;

    for (i = 0; i < node->ninp; i++) {
	if (!st_lookup(net->hash, node->inputs[i], &auxnd)) {
	    exit(2);
	}
	ntrCountDFS(net,auxnd);
    }

} /* end of ntrCountDFS */


/**Function********************************************************************

  Synopsis    [Computes the image of a set given a transition relation.]

  Description [Computes the image of a set given a transition relation.
  Returns a pointer to the result if successful; NULL otherwise. The image is
  returned in terms of the present state variables; its reference count is
  already increased.]

  SideEffects [None]

  SeeAlso     [Ntr_Trav]

******************************************************************************/
static DdNode *
ntrImage(
  DdManager * dd,
  NtrPartTR * TR,
  DdNode * from,
  NtrOptions * option)
{
    int i;
    DdNode *image;
    DdNode *to;
    NtrPartTR *T;
    int depth = 0;

    if (option->image == NTR_IMAGE_CLIP) {
	depth = (int) ((double) Cudd_ReadSize(dd) * option->imageClip);
    }

    /* Existentially quantify the present state variables that are not
    ** in the support of any next state function. */
    image = Cudd_bddExistAbstract(dd,from,TR->preiabs);
    if (image == NULL) return(NULL);
    Cudd_Ref(image);
    if (option->image == NTR_IMAGE_DEPEND) {
	/* Simplify the transition relation based on dependencies
	** and build the conjuncts from the deltas. */
	T = ntrEliminateDependencies(dd,TR,&image,option);
    } else {
	T = TR;
    }
    if (T == NULL) return(NULL);
    for (i = 0; i < T->nparts; i++) {
#if 0
	(void) printf("  Intermediate product[%d]: %d nodes\n",
		      i,Cudd_DagSize(image));
#endif
	if (option->image == NTR_IMAGE_CLIP) {
	    to = Cudd_bddClippingAndAbstract(dd,T->part[i],image,T->icube[i],
					     depth,option->approx);
	} else {
	    to = Cudd_bddAndAbstract(dd,T->part[i],image,T->icube[i]);
	}
	if (to == NULL) return(NULL);
	Cudd_Ref(to);
	if (option->image == NTR_IMAGE_DEPEND) {
	    /* Extract dependencies from intermediate product. */
	    DdNode *abs, *positive, *absabs, *phi, *exnor, *tmp;
	    abs = Cudd_bddExistAbstract(dd,to,T->xw);
	    if (abs == NULL) return(NULL); Cudd_Ref(abs);
	    if (Cudd_bddVarIsDependent(dd,abs,T->nscube[i]) &&
		Cudd_EstimateCofactor(dd,abs,T->nscube[i]->index,1) <=
		T->nlatches) {
		int retval, sizex;
		positive = Cudd_Cofactor(dd,abs,T->nscube[i]);
		if (positive == NULL) return(NULL); Cudd_Ref(positive);
		absabs = Cudd_bddExistAbstract(dd,abs,T->nscube[i]);
		if (absabs == NULL) return(NULL); Cudd_Ref(absabs);
		Cudd_RecursiveDeref(dd,abs);
		phi = Cudd_bddLICompaction(dd,positive,absabs);
		if (phi == NULL) return(NULL); Cudd_Ref(phi);
		Cudd_RecursiveDeref(dd,positive);
		Cudd_RecursiveDeref(dd,absabs);
		exnor = Cudd_bddXnor(dd,T->nscube[i],phi);
		if (exnor == NULL) return(NULL); Cudd_Ref(exnor);
		Cudd_RecursiveDeref(dd,phi);
		sizex = Cudd_DagSize(exnor);
		(void) printf("new factor of %d nodes\n", sizex);
		retval = Ntr_HeapInsert(T->factors,exnor,sizex);
		if (retval == 0) return(NULL);
		tmp = Cudd_bddExistAbstract(dd,to,T->nscube[i]);
		if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
		Cudd_RecursiveDeref(dd,to);
		to = tmp;
	    } else {
		Cudd_RecursiveDeref(dd,abs);
	    }
	}
	Cudd_RecursiveDeref(dd,image);
	image = to;
    }
    if (option->image == NTR_IMAGE_DEPEND) {
	int size1, size2;
	DdNode *factor1, *factor2, *tmp;
	int retval;
	size1 = Cudd_DagSize(image);
	retval = Ntr_HeapInsert(T->factors,image,size1);
	if (retval == 0) return(NULL);
	(void) printf("Merging %d factors. Independent image: %d nodes\n",
		      Ntr_HeapCount(T->factors), size1);
	while (Ntr_HeapCount(T->factors) > 1) {
	    retval = Ntr_HeapExtractMin(T->factors,&factor1,&size1);
	    if (retval == 0) return(NULL);
	    retval = Ntr_HeapExtractMin(T->factors,&factor2,&size2);
	    if (retval == 0) return(NULL);
	    tmp = Cudd_bddAnd(dd,factor1,factor2);
	    if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
	    size1 = Cudd_DagSize(tmp);
	    (void) printf("new factor %d nodes\n", size1);
	    Cudd_RecursiveDeref(dd,factor1);
	    Cudd_RecursiveDeref(dd,factor2);
	    retval = Ntr_HeapInsert(T->factors,tmp,size1);
	    if (retval == 0) return(NULL);
	}
	retval = Ntr_HeapExtractMin(T->factors,&image,&size1);
	if (retval == 0) return(NULL);
	Ntr_freeTR(dd,T);
    }

    /* Express image in terms of x variables. */
    to = Cudd_bddVarMap(dd,image);
    if (to == NULL) {
	Cudd_RecursiveDeref(dd,image);
	return(NULL);
    }
    Cudd_Ref(to);
    Cudd_RecursiveDeref(dd,image);
    return(to);

} /* end of ntrImage */


/**Function********************************************************************

  Synopsis    [Computes the preimage of a set given a transition relation.]

  Description [Computes the preimage of a set given a transition relation.
  Returns a pointer to the result if successful; NULL otherwise. The preimage
  is returned in terms of the next state variables; its reference count is
  already increased.]

  SideEffects [None]

  SeeAlso     [ntrImage Ntr_SCC]

******************************************************************************/
static DdNode *
ntrPreimage(
  DdManager * dd,
  NtrPartTR * T,
  DdNode * from)
{
    int i;
    DdNode *preimage;
    DdNode *to;

    /* Existentially quantify the present state variables that are not
    ** in the support of any next state function. */
    preimage = Cudd_bddExistAbstract(dd,from,T->prepabs);
    if (preimage == NULL) return(NULL);
    Cudd_Ref(preimage);
    for (i = 0; i < T->nparts; i++) {
#if 0
	(void) printf("  Intermediate product[%d]: %d nodes\n",
		      i,Cudd_DagSize(preimage));
#endif
	to = Cudd_bddAndAbstract(dd,T->part[i],preimage,T->pcube[i]);
	if (to == NULL) return(NULL);
	Cudd_Ref(to);
	Cudd_RecursiveDeref(dd,preimage);
	preimage = to;
    }

    /* Express preimage in terms of x variables. */
    to = Cudd_bddVarMap(dd,preimage);
    if (to == NULL) {
	Cudd_RecursiveDeref(dd,preimage);
	return(NULL);
    }
    Cudd_Ref(to);
    Cudd_RecursiveDeref(dd,preimage);
    return(to);

} /* end of ntrPreimage */


/**Function********************************************************************

  Synopsis    [Chooses the initial states for a BFS step.]

  Description [Chooses the initial states for a BFS step. Returns a
  pointer to the chose set if successful; NULL otherwise. The
  reference count of the result is already incremented.]

  SideEffects [none]

  SeeAlso     [Ntr_Trav]

******************************************************************************/
static DdNode *
ntrChooseFrom(
  DdManager * dd,
  DdNode * neW,
  DdNode * reached,
  NtrOptions * option)
{
    DdNode *min, *c;
    int threshold;

    switch (option->from) {
    case NTR_FROM_NEW:
	Cudd_Ref(neW);
	return(neW);
    case NTR_FROM_REACHED:
	Cudd_Ref(reached);
	return(reached);
    case NTR_FROM_RESTRICT:
	c = Cudd_bddOr(dd, neW, Cudd_Not(reached));
	if (c == NULL) return(NULL);
	Cudd_Ref(c);
	min = Cudd_bddRestrict(dd,neW,c);
	if (min == NULL) {
	    Cudd_RecursiveDeref(dd, c);
	    return(NULL);
	}
	Cudd_Ref(min);
	Cudd_RecursiveDeref(dd, c);
	return(min);
    case NTR_FROM_COMPACT:
	c = Cudd_bddOr(dd, neW, Cudd_Not(reached));
	if (c == NULL) return(NULL);
	Cudd_Ref(c);
	min = Cudd_bddLICompaction(dd,neW,c);
	if (min == NULL) {
	    Cudd_RecursiveDeref(dd, c);
	    return(NULL);
	}
	Cudd_Ref(min);
	Cudd_RecursiveDeref(dd, c);
	return(min);
    case NTR_FROM_SQUEEZE:
	min = Cudd_bddSqueeze(dd,neW,reached);
	if (min == NULL) return(NULL);
	Cudd_Ref(min);
	return(min);
    case NTR_FROM_UNDERAPPROX:
	threshold = (option->threshold < 0) ? 0 : option->threshold;
	min = Cudd_RemapUnderApprox(dd,neW,Cudd_SupportSize(dd,neW),
		threshold,option->quality);
	if (min == NULL) return(NULL);
	Cudd_Ref(min);
	return(min);
    case NTR_FROM_OVERAPPROX:
	threshold = (option->threshold < 0) ? 0 : option->threshold;
	min = Cudd_RemapOverApprox(dd,neW,Cudd_SupportSize(dd,neW),
		threshold,option->quality);
	if (min == NULL) return(NULL);
	Cudd_Ref(min);
	return(min);
    default:
	return(NULL);
    }

} /* end of ntrChooseFrom */


/**Function********************************************************************

  Synopsis    [Updates the reached states after a traversal step.]

  Description [Updates the reached states after a traversal
  step. Returns a pointer to the new reached set if successful; NULL
  otherwise. The reference count of the result is already incremented.]

  SideEffects [The old reached set is dereferenced.]

  SeeAlso     [Ntr_Trav]

******************************************************************************/
static DdNode *
ntrUpdateReached(
  DdManager * dd /* manager */,
  DdNode * oldreached /* old reached state set */,
  DdNode * to /* result of last image computation */)
{
    DdNode *reached;

    reached = Cudd_bddOr(dd,oldreached,to);
    if (reached == NULL) {
	Cudd_RecursiveDeref(dd,oldreached);
	return(NULL);
    }
    Cudd_Ref(reached);
    Cudd_RecursiveDeref(dd,oldreached);
    return(reached);

} /* end of ntrUpdateReached */


/**Function********************************************************************

  Synopsis    [Analyzes the reached states after traversal to find
  dependent latches.]

  Description [Analyzes the reached states after traversal to find
  dependent latches.  Returns the number of latches that can be
  eliminated because they are stuck at a constant value or are
  dependent on others if successful; -1 otherwise. The algorithm is
  greedy and determines a local optimum, not a global one.]

  SideEffects []

  SeeAlso     [Ntr_Trav]

******************************************************************************/
static int
ntrLatchDependencies(
  DdManager *dd,
  DdNode *reached,
  BnetNetwork *net,
  NtrOptions *option)
{
    int i;
    int howMany;		/* number of latches that can be eliminated */
    DdNode *var, *newreached, *abs, *positive, *phi;
    char *name;
    BnetNode *node;
    int initVars, finalVars;
    double initStates, finalStates;
    DdNode **roots;
    char **onames;
    int howManySmall = 0;
    int *candidates;
    double minStates;
    int totalVars;

    (void) printf("Analyzing latch dependencies\n");
    roots = ALLOC(DdNode *, net->nlatches);
    if (roots == NULL) return(-1);
    onames = ALLOC(char *, net->nlatches);
    if (onames == NULL) return(-1);

    candidates = ALLOC(int,net->nlatches);
    if (candidates == NULL) return(-1);
    for (i = 0; i < net->nlatches; i++) {
	candidates[i] = i;
    }
    /* The signatures of the variables in a function are the number
    ** of minterms of the positive cofactors with respect to the
    ** variables themselves. */
    newreached = reached;
    Cudd_Ref(newreached);
    signatures = Cudd_CofMinterm(dd,newreached);
    if (signatures == NULL) return(-1);
    /* We now extract a positive quantity which is higher for those
    ** variables that are closer to being essential. */
    totalVars = Cudd_ReadSize(dd);
    minStates = signatures[totalVars];
#if 0
    (void) printf("Raw signatures (minStates = %g)\n", minStates);
    for (i = 0; i < net->nlatches; i++) {
	int j = candidates[i];
	if (!st_lookup(net->hash,net->latches[j][1],(char **) &node)) {
	    return(-1);
	}
	(void) printf("%s -> %g\n", node->name, signatures[node->dd->index]);
    }
#endif
    for (i = 0; i < totalVars; i++) {
	double z = signatures[i] / minStates - 1.0;
	signatures[i] = (z >= 0.0) ? z : -z;	/* make positive */
    }
    staticNet = net;
    qsort((void *)candidates,net->nlatches,sizeof(int),
	  (DD_QSFP)ntrSignatureCompare2);
#if 0
    (void) printf("Cooked signatures\n");
    for (i = 0; i < net->nlatches; i++) {
	int j = candidates[i];
	if (!st_lookup(net->hash,net->latches[j][1],(char **) &node)) {
	    return(-1);
	}
	(void) printf("%s -> %g\n", node->name, signatures[node->dd->index]);
    }
#endif
    FREE(signatures);

    /* Extract simple dependencies. */
    for (i = 0; i < net->nlatches; i++) {
	int j = candidates[i];
	if (!st_lookup(net->hash,net->latches[j][1],&node)) {
	    return(-1);
	}
	var = node->dd;
	name = node->name;
	if (Cudd_bddVarIsDependent(dd,newreached,var)) {
	    positive = Cudd_Cofactor(dd,newreached,var);
	    if (positive == NULL) return(-1); Cudd_Ref(positive);
	    abs = Cudd_bddExistAbstract(dd,newreached,var);
	    if (abs == NULL) return(-1); Cudd_Ref(abs);
	    phi = Cudd_bddLICompaction(dd,positive,abs);
	    if (phi == NULL) return(-1); Cudd_Ref(phi);
	    Cudd_RecursiveDeref(dd,positive);
	    if (Cudd_DagSize(phi) < NTR_MAX_DEP_SIZE) {
		if (Cudd_bddLeq(dd,newreached,var)) {
		    (void) printf("%s is stuck at 1\n",name);
		} else if (Cudd_bddLeq(dd,newreached,Cudd_Not(var))) {
		    (void) printf("%s is stuck at 0\n",name);
		} else {
		    (void) printf("%s depends on the other variables\n",name);
		}
		roots[howManySmall] = phi;
		onames[howManySmall] = util_strsav(name);
		Cudd_RecursiveDeref(dd,newreached);
		newreached = abs;
		howManySmall++;
		candidates[i] = -1; /* do not reconsider */
	    } else {
		Cudd_RecursiveDeref(dd,abs);
		Cudd_RecursiveDeref(dd,phi);
	    }
	} else {
	    candidates[i] = -1;	/* do not reconsider */
	}
    }
    /* Now remove remaining dependent variables. */
    howMany = howManySmall;
    for (i = 0; i < net->nlatches; i++) {
	int j = candidates[i];
	if (j == -1) continue;
	if (!st_lookup(net->hash,net->latches[j][1],&node)) {
	    return(-1);
	}
	var = node->dd;
	name = node->name;
	if (Cudd_bddVarIsDependent(dd,newreached,var)) {
	    if (Cudd_bddLeq(dd,newreached,var)) {
		(void) printf("%s is stuck at 1\n",name);
	    } else if (Cudd_bddLeq(dd,newreached,Cudd_Not(var))) {
		(void) printf("%s is stuck at 0\n",name);
	    } else {
		(void) printf("%s depends on the other variables\n",name);
	    }
	    abs = Cudd_bddExistAbstract(dd,newreached,var);
	    if (abs == NULL) return(-1); Cudd_Ref(abs);
	    Cudd_RecursiveDeref(dd,newreached);
	    newreached = abs;
	    howMany++;
	}
    }
    FREE(candidates);
    if (howManySmall > 0) {
	if (!Bnet_bddArrayDump(dd,net,(char *)"-",roots,onames,howManySmall,1))
	    return(-1);
    }
    for (i = 0; i < howManySmall; i++) {
	Cudd_RecursiveDeref(dd,roots[i]);
	FREE(onames[i]);
    }
    FREE(roots);
    FREE(onames);

    initVars = net->nlatches;
    initStates = Cudd_CountMinterm(dd,reached,initVars);
    finalVars = initVars - howMany;
    finalStates = Cudd_CountMinterm(dd,newreached,finalVars);
    if (initStates != finalStates) {
	(void) printf("Error: the number of states changed from %g to %g\n",
		      initStates, finalStates);
	return(-1);
    }
    (void) printf("new reached");
    Cudd_PrintDebug(dd,newreached,finalVars,option->verb);
    Cudd_RecursiveDeref(dd,newreached);
    return(howMany);

} /* end of ntrLatchDependencies */


/**Function********************************************************************

  Synopsis    [Eliminates dependent variables from a transition relation.]

  Description [Eliminates dependent variables from a transition
  relation.  Returns a simplified copy of the given transition
  relation if successful; NULL otherwise.]

  SideEffects [The modified set of states is returned as a side effect.]

  SeeAlso     [ntrImage]

******************************************************************************/
static NtrPartTR *
ntrEliminateDependencies(
  DdManager *dd,
  NtrPartTR *TR,
  DdNode **states,
  NtrOptions *option)
{
    NtrPartTR *T;		/* new TR without dependent vars */
    int pr = option->verb;
    int i, j;
    int howMany = 0;		/* number of latches that can be eliminated */
    DdNode *var, *newstates, *abs, *positive, *phi;
    DdNode *support, *scan, *tmp;
    int finalSize;		/* size of the TR after substitutions */
    int nvars;			/* vars in the support of the state set */
    int *candidates;		/* vars to be considered for elimination */
    int totalVars;
    double minStates;

    /* Initialize the new transition relation by copying the old one. */
    T = Ntr_cloneTR(TR);
    if (T == NULL) return(NULL);
    newstates = *states;
    Cudd_Ref(newstates);

    /* Find and rank the candidate variables. */
    support = Cudd_Support(dd,newstates);
    if (support == NULL) {
	Ntr_freeTR(dd,T);
	return(NULL);
    }
    Cudd_Ref(support);
    nvars = Cudd_DagSize(support) - 1;
    candidates = ALLOC(int,nvars);
    if (candidates == NULL) {
	Cudd_RecursiveDeref(dd,support);
	Ntr_freeTR(dd,T);
	return(NULL);
    }
    scan  = support;
    for (i = 0; i < nvars; i++) {
	candidates[i] = scan->index;
	scan = Cudd_T(scan);
    }
    Cudd_RecursiveDeref(dd,support);
    /* The signatures of the variables in a function are the number
    ** of minterms of the positive cofactors with respect to the
    ** variables themselves. */
    signatures = Cudd_CofMinterm(dd,newstates);
    if (signatures == NULL) {
	FREE(candidates);
	Ntr_freeTR(dd,T);
	return(NULL);
    }
    /* We now extract a positive quantity which is higher for those
    ** variables that are closer to being essential. */
    totalVars = Cudd_ReadSize(dd);
    minStates = signatures[totalVars];
    for (i = 0; i < totalVars; i++) {
	double z = signatures[i] / minStates - 1.0;
	signatures[i] = (z < 0.0) ? -z : z;	/* make positive */
    }
    /* Sort candidates in decreasing order of signature. */
    qsort((void *)candidates,nvars,sizeof(int),
	  (DD_QSFP)ntrSignatureCompare);
    FREE(signatures);

    /* Now process the candidates in the given order. */
    for (i = 0; i < nvars; i++) {
	var = Cudd_bddIthVar(dd,candidates[i]);
	if (Cudd_bddVarIsDependent(dd,newstates,var)) {
	    abs = Cudd_bddExistAbstract(dd,newstates,var);
	    if (abs == NULL) return(NULL); Cudd_Ref(abs);
	    positive = Cudd_Cofactor(dd,newstates,var);
	    if (positive == NULL) return(NULL); Cudd_Ref(positive);
	    phi = Cudd_bddLICompaction(dd,positive,abs);
	    if (phi == NULL) return(NULL); Cudd_Ref(phi);
	    Cudd_RecursiveDeref(dd,positive);
#if 0
	    if (pr > 0) {
		(void) printf("Phi");
		Cudd_PrintDebug(dd,phi,T->nlatches,pr);
	    }
#endif
	    if (Cudd_DagSize(phi) < NTR_MAX_DEP_SIZE) {
		howMany++;
		for (j = 0; j < T->nparts; j++) {
		    tmp = Cudd_bddCompose(dd,T->part[j],phi,candidates[i]);
		    if (tmp == NULL) return(NULL); Cudd_Ref(tmp);
		    Cudd_RecursiveDeref(dd,T->part[j]);
		    T->part[j] = tmp;
		}
		Cudd_RecursiveDeref(dd,newstates);
		newstates = abs;
	    } else {
		Cudd_RecursiveDeref(dd,abs);
	    }
	    Cudd_RecursiveDeref(dd,phi);
	}
    }
    FREE(candidates);

    if (pr > 0) {
	finalSize = Cudd_SharingSize(T->part,T->nparts);
	(void) printf("Eliminated %d vars. Transition function %d nodes.\n",
		      howMany,finalSize);
    }

    if (!ntrUpdateQuantificationSchedule(dd,T)) return(NULL);

    /* Quantify out of states variables that no longer appear in any part. */
    Cudd_RecursiveDeref(dd,*states);
    *states = Cudd_bddExistAbstract(dd,newstates,T->preiabs);
    if (*states == NULL) return(NULL); Cudd_Ref(*states);
    Cudd_RecursiveDeref(dd,newstates);
    return(T);

} /* end of ntrEliminateDependencies */


/**Function********************************************************************

  Synopsis    [Updates the quantification schedule of a transition relation.]

  Description [Updates the quantification schedule of a transition relation.
  Returns 1 if successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     [ntrEliminateDependencies]

******************************************************************************/
static int
ntrUpdateQuantificationSchedule(
  DdManager *dd,
  NtrPartTR *T)
{
    int i, j, k;
    int *schedule;
    DdNode *one, *support, *scan, *var, *tmp;
    char **matrix;
    int *position, *row;
    char *flags;
    int nparts, nvars;
    int extracted;
#if 0
    int schedcost;
#endif

    nparts = T->nparts;
    nvars = Cudd_ReadSize(dd);
    one = Cudd_ReadOne(dd);

    /* Reinitialize the abstraction cubes. */
    Cudd_RecursiveDeref(dd,T->preiabs);
    T->preiabs = one;
    Cudd_Ref(one);
    for (i = 0; i < nparts; i++) {
	Cudd_RecursiveDeref(dd,T->icube[i]);
	T->icube[i] = one;
	Cudd_Ref(one);
    }

    /* Initialize row permutations to the identity. */
    position = ALLOC(int,nparts);
    if (position == NULL) return(0);
    for (i = 0; i < nparts; i++) {
	position[i] = i;
    }
    /* Sort parts so that parts that differ only
    ** in the index of the next state variable are contiguous. */
    staticPart = T->part;
    qsort((void *)position,nparts,sizeof(int), (DD_QSFP)ntrPartCompare);
    /* Extract repeated parts. */
    extracted = 0;
    for (i = 0; i < nparts - 1; i += j) {
	int pi, pij;
	DdNode *eq;
	j = 1;
	pi = position[i];
	eq = one;
	Cudd_Ref(eq);
	pij = position[i+j];
	while (Cudd_Regular(staticPart[pij]) == Cudd_Regular(staticPart[pi])) {
	    int comple = staticPart[pij] != staticPart[pi];
	    DdNode *xnor = Cudd_bddXnor(dd,T->nscube[pi],
					Cudd_NotCond(T->nscube[pij],comple));
	    if (xnor == NULL) return(0); Cudd_Ref(xnor);
	    tmp = Cudd_bddAnd(dd,xnor,eq);
	    if (tmp == NULL) return(0); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,xnor);
	    Cudd_RecursiveDeref(dd,eq);
	    eq = tmp;
	    Cudd_RecursiveDeref(dd,T->part[pij]);
	    Cudd_RecursiveDeref(dd,T->icube[pij]);
	    Cudd_RecursiveDeref(dd,T->nscube[pij]);
	    T->part[pij] = NULL;
	    j++;
	    if (i+j == nparts) break;
	    pij = position[i+j];
	}
	if (eq != one) {
	    int retval = Ntr_HeapInsert(T->factors,eq,Cudd_DagSize(eq));
	    if (retval == 0) return(0);
	    extracted += j - 1;
	} else {
	    Cudd_RecursiveDeref(dd,eq);
	}
    }
    /* Compact the part array by removing extracted parts. */
    for (i = 0, j = 0; i < nparts; i++) {
	if (T->part[i] != NULL) {
	    T->part[j] = T->part[i];
	    T->icube[j] = T->icube[i];
	    T->nscube[j] = T->nscube[i];
	    j++;
	}
    }
    nparts = T->nparts -= extracted;
    (void) printf("Extracted %d repeated parts in %d factors.\n",
		  extracted, Ntr_HeapCount(T->factors));

    /* Build the support matrix. Each row corresponds to a part of the
    ** transition relation; each column corresponds to a variable in
    ** the manager. A 1 in position (i,j) means that Part i depends
    ** on Variable j. */
    matrix = ntrAllocMatrix(nparts,nvars);
    if (matrix == NULL) return(0);

    /* Allocate array for quantification schedule and initialize it. */
    schedule = ALLOC(int,nvars);
    if (schedule == NULL) return(0);
    for (i = 0; i < nvars; i++) {
	schedule[i] = -1;
    }
    /* Collect scheduling info for this part. At the end of this loop
    ** schedule[i] == j means that the variable of index i does not
    ** appear in any part with index greater than j, unless j == -1,
    ** in which case the variable appears in no part.
    */
    for (i = 0; i < nparts; i++) {
	support = Cudd_Support(dd,T->part[i]);
	if (support == NULL) return(0); Cudd_Ref(support);
	scan = support;
	while (!Cudd_IsConstant(scan)) {
	    int index = scan->index;
	    schedule[index] = i;
	    matrix[i][index] = 1;
	    scan = Cudd_T(scan);
	}
	Cudd_RecursiveDeref(dd,support);
    }
#if 0
    (void) printf("Initial schedule:");
    schedcost = 0;
    for (i = 0; i < nvars; i++) {
	(void) printf(" %d", schedule[i]);
	if (schedule[i] != -1) schedcost += schedule[i];
    }
    (void) printf("\nCost = %d\n", schedcost);
#endif

    /* Initialize direct and inverse row permutations to the identity
    ** permutation. */
    row = ALLOC(int,nparts);
    if (row == NULL) return(0);
    for (i = 0; i < nparts; i++) {
	position[i] = row[i] = i;
    }

    /* Sift the matrix. */
    flags = ALLOC(char,nvars);
    if (flags == NULL) return(0);
    for (i = 0; i < nparts; i++) {
	int cost = 0;		/* cost of moving the row */
	int bestcost = 0;
	int posn = position[i];
	int bestposn = posn;
	/* Sift up. */
	/* Initialize the flags to one is for the variables that are
	** currently scheduled to be quantified after this part gets
	** multiplied. When we cross a row of a part that depends on
	** a variable whose flag is 1, we know that the row being sifted
	** is no longer responsible for that variable. */
	for (k = 0; k < nvars; k++) {
	    flags[k] = (char) (schedule[k] == i);
	}
	for (j = posn - 1; j >= 0; j--) {
	    for (k = 0; k < nvars; k++) {
		if (schedule[k] == row[j]) {
		    cost++;
		} else {
		    flags[k] &= matrix[row[j]][k] == 0;
		    cost -= flags[k];
		}
	    }
	    if (cost < bestcost) {
		bestposn = j;
		bestcost = cost;
	    }
	}
	/* Sift down. */
	/* Reinitialize the flags. (We are implicitly undoing the sift
	** down step.) */
	for (k = 0; k < nvars; k++) {
	    flags[k] = (char) (schedule[k] == i);
	}
	for (j = posn + 1; j < nparts; j++) {
	    for (k = 0; k < nvars; k++) {
		if (schedule[k] == row[j]) {
		    flags[k] |= matrix[i][k] == 1;
		    cost -= flags[k] == 0;
		} else {
		    cost += flags[k];
		}
	    }
	    if (cost < bestcost) {
		bestposn = j;
		bestcost = cost;
	    }
	}
	/* Move to best position. */
	if (bestposn < posn) {
	    for (j = posn; j >= bestposn; j--) {
		k = row[j];
		if (j > 0) row[j] = row[j-1];
		position[k]++;
	    }
	} else {
	    for (j = posn; j <= bestposn; j++) {
		k = row[j];
		if (j < nparts - 1) row[j] = row[j+1];
		position[k]--;
	    }
	}
	position[i] = bestposn;
	row[bestposn] = i;
	/* Fix the schedule. */
	for (k = 0; k < nvars; k++) {
	    if (matrix[i][k] == 1) {
		if (position[schedule[k]] < bestposn) {
		    schedule[k] = i;
		} else {
		    for (j = nparts - 1; j >= position[i]; j--) {
			if (matrix[row[j]][k] == 1) break;
		    }
		    schedule[k] = row[j];
		}
	    }
	}
    }
    ntrFreeMatrix(matrix);
    FREE(flags);

    /* Update schedule to account for the permutation. */
    for (i = 0; i < nvars; i++) {
	if (schedule[i] >= 0) {
	    schedule[i] = position[schedule[i]];
	}
    }
    /* Sort parts. */
    ntrPermuteParts(T->part,T->nscube,row,position,nparts);
    FREE(position);
    FREE(row);
#if 0
    (void) printf("New schedule:");
    schedcost = 0;
    for (i = 0; i < nvars; i++) {
	(void) printf(" %d", schedule[i]);
	if (schedule[i] != -1) schedcost += schedule[i];
    }
    (void) printf("\nCost = %d\n", schedcost);
#endif

    /* Mark the next state varibles so that they do not go in the
    ** abstraction cubes. */
    for (i = 0; i < T->nlatches; i++) {
	schedule[T->y[i]->index] = -2;
    }

    /* Rebuild the cubes from the schedule. */
    for (i = 0; i < nvars; i++) {
	k = schedule[i];
	var = Cudd_bddIthVar(dd,i);
	if (k >= 0) {
	    tmp = Cudd_bddAnd(dd,T->icube[k],var);
	    if (tmp == NULL) return(0); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,T->icube[k]);
	    T->icube[k] = tmp;
	} else if (k != -2) {
	    tmp = Cudd_bddAnd(dd,T->preiabs,var);
	    if (tmp == NULL) return(0); Cudd_Ref(tmp);
	    Cudd_RecursiveDeref(dd,T->preiabs);
	    T->preiabs = tmp;
	}
    }
    FREE(schedule);

    /* Build the conjuncts. */
    for (i = 0; i < nparts; i++) {
	tmp = Cudd_bddXnor(dd,T->nscube[i],T->part[i]);
	if (tmp == NULL) return(0); Cudd_Ref(tmp);
	Cudd_RecursiveDeref(dd,T->part[i]);
	T->part[i] = tmp;
    }

    return(1);

} /* end of ntrUpdateQuantificationSchedule */


/**Function********************************************************************

  Synopsis    [Comparison function used by qsort.]

  Description [Comparison function used by qsort to order the
  variables according to their signatures.]

  SideEffects [None]

******************************************************************************/
static int
ntrSignatureCompare(
  int * ptrX,
  int * ptrY)
{
    if (signatures[*ptrY] > signatures[*ptrX]) return(1);
    if (signatures[*ptrY] < signatures[*ptrX]) return(-1);
    return(0);

} /* end of ntrSignatureCompare */


/**Function********************************************************************

  Synopsis    [Comparison function used by qsort.]

  Description [Comparison function used by qsort to order the
  variables according to their signatures.]

  SideEffects [None]

******************************************************************************/
static int
ntrSignatureCompare2(
  int * ptrX,
  int * ptrY)
{
    BnetNode *node;
    int x,y;
    if (!st_lookup(staticNet->hash,staticNet->latches[*ptrX][1],&node)) {
	return(0);
    }
    x = node->dd->index;
    if (!st_lookup(staticNet->hash,staticNet->latches[*ptrY][1],&node)) {
	return(0);
    }
    y = node->dd->index;
    if (signatures[x] < signatures[y]) return(1);
    if (signatures[x] > signatures[y]) return(-1);
    return(0);

} /* end of ntrSignatureCompare2 */


/**Function********************************************************************

  Synopsis    [Comparison function used by qsort.]

  Description [Comparison function used by qsort to order the
  parts according to the BDD addresses.]

  SideEffects [None]

******************************************************************************/
static int
ntrPartCompare(
  int * ptrX,
  int * ptrY)
{
    if (staticPart[*ptrY] > staticPart[*ptrX]) return(1);
    if (staticPart[*ptrY] < staticPart[*ptrX]) return(-1);
    return(0);

} /* end of ntrPartCompare */


/**Function********************************************************************

  Synopsis    [Allocates a matrix.]

  Description [Allocates a matrix of char's. Returns a pointer to the matrix
  if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static char **
ntrAllocMatrix(
  int nrows,
  int ncols)
{
    int i;
    char **matrix;

    matrix = ALLOC(char *,nrows);
    if (matrix == NULL) return(NULL);
    matrix[0] = ALLOC(char,nrows * ncols);
    if (matrix[0] == NULL) {
	FREE(matrix);
	return(NULL);
    }
    for (i = 1; i < nrows; i++) {
	matrix[i] = matrix[i-1] + ncols;
    }
    for (i = 0; i < nrows * ncols; i++) {
	matrix[0][i] = 0;
    }
    return(matrix);

} /* end of ntrAllocMatrix */


/**Function********************************************************************

  Synopsis    [Frees a matrix of char's.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static void
ntrFreeMatrix(
  char **matrix)
{
    FREE(matrix[0]);
    FREE(matrix);
    return;

} /* end of ntrFreeMatrix */


/**Function********************************************************************

  Synopsis    [Sorts parts according to given permutation.]

  Description []

  SideEffects [The permutation arrays are turned into the identity
  permutations.]

  SeeAlso     []

******************************************************************************/
static void
ntrPermuteParts(
  DdNode **a,
  DdNode **b,
  int *comesFrom,
  int *goesTo,
  int size)
{
    int i, j;
    DdNode *tmp;

    for (i = 0; i < size; i++) {
	if (comesFrom[i] == i) continue;
	j = comesFrom[i];
	tmp = a[i]; a[i] = a[j]; a[j] = tmp;
	tmp = b[i]; b[i] = b[j]; b[j] = tmp;
	comesFrom[goesTo[i]] = j;
	comesFrom[i] = i;
	goesTo[j] = goesTo[i];
	goesTo[i] = i;
    }
    return;

} /* end of ntrPermuteParts */
