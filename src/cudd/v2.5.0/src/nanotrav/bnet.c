/**CFile***********************************************************************

  FileName    [bnet.c]

  PackageName [bnet]

  Synopsis    [Functions to read in a boolean network.]

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

#include "bnet.h"

/*---------------------------------------------------------------------------*/
/* Constant declarations                                                     */
/*---------------------------------------------------------------------------*/

#define MAXLENGTH 131072

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
static char rcsid[] UTIL_UNUSED = "$Id: bnet.c,v 1.26 2012/02/05 01:53:01 fabio Exp fabio $";
#endif

static	char	BuffLine[MAXLENGTH];
static	char	*CurPos;
static	int	newNameNumber = 0;

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static char * readString (FILE *fp);
static char ** readList (FILE *fp, int *n);
static void printList (char **list, int n);
static char ** bnetGenerateNewNames (st_table *hash, int n);
static int bnetDumpReencodingLogic (DdManager *dd, char *mname, int noutputs, DdNode **outputs, char **inames, char **altnames, char **onames, FILE *fp);
#if 0
static int bnetBlifXnorTable (FILE *fp, int n);
#endif
static int bnetBlifWriteReencode (DdManager *dd, char *mname, char **inames, char **altnames, int *support, FILE *fp);
static int * bnetFindVectorSupport (DdManager *dd, DdNode **list, int n);
static int buildExorBDD (DdManager *dd, BnetNode *nd, st_table *hash, int params, int nodrop);
static int buildMuxBDD (DdManager * dd, BnetNode * nd, st_table * hash, int  params, int  nodrop);
static int bnetSetLevel (BnetNetwork *net);
static int bnetLevelDFS (BnetNetwork *net, BnetNode *node);
static BnetNode ** bnetOrderRoots (BnetNetwork *net, int *nroots);
static int bnetLevelCompare (BnetNode **x, BnetNode **y);
static int bnetDfsOrder (DdManager *dd, BnetNetwork *net, BnetNode *node);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Reads boolean network from blif file.]

  Description [Reads a boolean network from a blif file. A very restricted
  subset of blif is supported. Specifically:
  <ul>
  <li> The only directives recognized are:
    <ul>
    <li> .model
    <li> .inputs
    <li> .outputs
    <li> .latch
    <li> .names
    <li> .exdc
    <li> .wire_load_slope
    <li> .end
    </ul>
  <li> Latches must have an initial values and no other parameters
       specified.
  <li> Lines must not exceed MAXLENGTH-1 characters, and individual names must
       not exceed 1023 characters.
  </ul>
  Caveat emptor: There may be other limitations as well. One should
  check the syntax of the blif file with some other tool before relying
  on this parser. Bnet_ReadNetwork returns a pointer to the network if
  successful; NULL otherwise.
  ]

  SideEffects [None]

  SeeAlso     [Bnet_PrintNetwork Bnet_FreeNetwork]

******************************************************************************/
BnetNetwork *
Bnet_ReadNetwork(
  FILE * fp /* pointer to the blif file */,
  int  pr /* verbosity level */)
{
    char *savestring;
    char **list;
    int i, j, n;
    BnetNetwork *net;
    BnetNode *newnode;
    BnetNode *lastnode = NULL;
    BnetTabline *newline;
    BnetTabline *lastline;
    char ***latches = NULL;
    int maxlatches = 0;
    int exdc = 0;
    BnetNode	*node;
    int	count;

    /* Allocate network object and initialize symbol table. */
    net = ALLOC(BnetNetwork,1);
    if (net == NULL) goto failure;
    memset((char *) net, 0, sizeof(BnetNetwork));
    net->hash = st_init_table(strcmp,st_strhash);
    if (net->hash == NULL) goto failure;

    savestring = readString(fp);
    if (savestring == NULL) goto failure;
    net->nlatches = 0;
    while (strcmp(savestring, ".model") == 0 ||
	strcmp(savestring, ".inputs") == 0 ||
	strcmp(savestring, ".outputs") == 0 ||
	strcmp(savestring, ".latch") == 0 ||
	strcmp(savestring, ".wire_load_slope") == 0 ||
	strcmp(savestring, ".exdc") == 0 ||
	strcmp(savestring, ".names") == 0 || strcmp(savestring,".end") == 0) {
	if (strcmp(savestring, ".model") == 0) {
	    /* Read .model directive. */
	    FREE(savestring);
	    /* Read network name. */
	    savestring = readString(fp);
	    if (savestring == NULL) goto failure;
	    net->name = savestring;
	} else if (strcmp(savestring, ".inputs") == 0) {
	    /* Read .inputs directive. */
	    FREE(savestring);
	    /* Read input names. */
	    list = readList(fp,&n);
	    if (list == NULL) goto failure;
	    if (pr > 2) printList(list,n);
	    /* Expect at least one input. */
	    if (n < 1) {
		(void) fprintf(stdout,"Empty input list.\n");
		goto failure;
	    }
	    if (exdc) {
		for (i = 0; i < n; i++)
		    FREE(list[i]);
		FREE(list);
		savestring = readString(fp);
		if (savestring == NULL) goto failure;
		continue;
	    }
	    if (net->ninputs) {
		net->inputs = REALLOC(char *, net->inputs,
		    (net->ninputs + n) * sizeof(char *));
		for (i = 0; i < n; i++)
		    net->inputs[net->ninputs + i] = list[i];
	    }
	    else
		net->inputs = list;
	    /* Create a node for each primary input. */
	    for (i = 0; i < n; i++) {
		newnode = ALLOC(BnetNode,1);
		memset((char *) newnode, 0, sizeof(BnetNode));
		if (newnode == NULL) goto failure;
		newnode->name = list[i];
		newnode->inputs = NULL;
		newnode->type = BNET_INPUT_NODE;
		newnode->active = FALSE;
		newnode->nfo = 0;
		newnode->ninp = 0;
		newnode->f = NULL;
		newnode->polarity = 0;
		newnode->dd = NULL;
		newnode->next = NULL;
		if (lastnode == NULL) {
		    net->nodes = newnode;
		} else {
		    lastnode->next = newnode;
		}
		lastnode = newnode;
	    }
	    net->npis += n;
	    net->ninputs += n;
	} else if (strcmp(savestring, ".outputs") == 0) {
	    /* Read .outputs directive. We do not create nodes for the primary
	    ** outputs, because the nodes will be created when the same names
	    ** appear as outputs of some gates.
	    */
	    FREE(savestring);
	    /* Read output names. */
	    list = readList(fp,&n);
	    if (list == NULL) goto failure;
	    if (pr > 2) printList(list,n);
	    if (n < 1) {
		(void) fprintf(stdout,"Empty .outputs list.\n");
		goto failure;
	    }
	    if (exdc) {
		for (i = 0; i < n; i++)
		    FREE(list[i]);
		FREE(list);
		savestring = readString(fp);
		if (savestring == NULL) goto failure;
		continue;
	    }
	    if (net->noutputs) {
		net->outputs = REALLOC(char *, net->outputs,
		    (net->noutputs + n) * sizeof(char *));
		for (i = 0; i < n; i++)
		    net->outputs[net->noutputs + i] = list[i];
	    } else {
		net->outputs = list;
	    }
	    net->npos += n;
	    net->noutputs += n;
	} else if (strcmp(savestring,".wire_load_slope") == 0) {
	    FREE(savestring);
	    savestring = readString(fp);
	    net->slope = savestring;
	} else if (strcmp(savestring,".latch") == 0) {
	    FREE(savestring);
	    newnode = ALLOC(BnetNode,1);
	    if (newnode == NULL) goto failure;
	    memset((char *) newnode, 0, sizeof(BnetNode));
	    newnode->type = BNET_PRESENT_STATE_NODE;
	    list = readList(fp,&n);
	    if (list == NULL) goto failure;
	    if (pr > 2) printList(list,n);
	    /* Expect three names. */
	    if (n != 3) {
		(void) fprintf(stdout,
			       ".latch not followed by three tokens.\n");
		goto failure;
	    }
	    newnode->name = list[1];
	    newnode->inputs = NULL;
	    newnode->ninp = 0;
	    newnode->f = NULL;
	    newnode->active = FALSE;
	    newnode->nfo = 0;
	    newnode->polarity = 0;
	    newnode->dd = NULL;
	    newnode->next = NULL;
	    if (lastnode == NULL) {
		net->nodes = newnode;
	    } else {
		lastnode->next = newnode;
	    }
	    lastnode = newnode;
	    /* Add next state variable to list. */
	    if (maxlatches == 0) {
		maxlatches = 20;
		latches = ALLOC(char **,maxlatches);
	    } else if (maxlatches <= net->nlatches) {
		maxlatches += 20;
		latches = REALLOC(char **,latches,maxlatches);
	    }
	    latches[net->nlatches] = list;
	    net->nlatches++;
	    savestring = readString(fp);
	    if (savestring == NULL) goto failure;
	} else if (strcmp(savestring,".names") == 0) {
	    FREE(savestring);
	    newnode = ALLOC(BnetNode,1);
	    memset((char *) newnode, 0, sizeof(BnetNode));
	    if (newnode == NULL) goto failure;
	    list = readList(fp,&n);
	    if (list == NULL) goto failure;
	    if (pr > 2) printList(list,n);
	    /* Expect at least one name (the node output). */
	    if (n < 1) {
		(void) fprintf(stdout,"Missing output name.\n");
		goto failure;
	    }
	    newnode->name = list[n-1];
	    newnode->inputs = list;
	    newnode->ninp = n-1;
	    newnode->active = FALSE;
	    newnode->nfo = 0;
	    newnode->polarity = 0;
	    if (newnode->ninp > 0) {
		newnode->type = BNET_INTERNAL_NODE;
		for (i = 0; i < net->noutputs; i++) {
		    if (strcmp(net->outputs[i], newnode->name) == 0) {
			newnode->type = BNET_OUTPUT_NODE;
			break;
		    }
		}
	    } else {
		newnode->type = BNET_CONSTANT_NODE;
	    }
	    newnode->dd = NULL;
	    newnode->next = NULL;
	    if (lastnode == NULL) {
		net->nodes = newnode;
	    } else {
		lastnode->next = newnode;
	    }
	    lastnode = newnode;
	    /* Read node function. */
	    newnode->f = NULL;
	    if (exdc) {
		newnode->exdc_flag = 1;
		node = net->nodes;
		while (node) {
		    if (node->type == BNET_OUTPUT_NODE &&
			strcmp(node->name, newnode->name) == 0) {
			node->exdc = newnode;
			break;
		    }
		    node = node->next;
		}
	    }
	    savestring = readString(fp);
	    if (savestring == NULL) goto failure;
	    lastline = NULL;
	    while (savestring[0] != '.') {
		/* Reading a table line. */
		newline = ALLOC(BnetTabline,1);
		if (newline == NULL) goto failure;
		newline->next = NULL;
		if (lastline == NULL) {
		    newnode->f = newline;
		} else {
		    lastline->next = newline;
		}
		lastline = newline;
		if (newnode->type == BNET_INTERNAL_NODE ||
		    newnode->type == BNET_OUTPUT_NODE) {
		    newline->values = savestring;
		    /* Read output 1 or 0. */
		    savestring = readString(fp);
		    if (savestring == NULL) goto failure;
		} else {
		    newline->values = NULL;
		}
		if (savestring[0] == '0') newnode->polarity = 1;
		FREE(savestring);
		savestring = readString(fp);
		if (savestring == NULL) goto failure;
	    }
	} else if (strcmp(savestring,".exdc") == 0) {
	    FREE(savestring);
	    exdc = 1;
	} else if (strcmp(savestring,".end") == 0) {
	    FREE(savestring);
	    break;
	}
	if ((!savestring) || savestring[0] != '.')
	    savestring = readString(fp);
	if (savestring == NULL) goto failure;
    }

    /* Put nodes in symbol table. */
    newnode = net->nodes;
    while (newnode != NULL) {
	int retval = st_insert(net->hash,newnode->name,(char *) newnode);
	if (retval == ST_OUT_OF_MEM) {
	    goto failure;
	} else if (retval == 1) {
	    printf("Error: Multiple drivers for node %s\n", newnode->name);
	    goto failure;
	} else {
	    if (pr > 2) printf("Inserted %s\n",newnode->name);
	}
	newnode = newnode->next;
    }

    if (latches) {
	net->latches = latches;

	count = 0;
	net->outputs = REALLOC(char *, net->outputs,
	    (net->noutputs + net->nlatches) * sizeof(char *));
	for (i = 0; i < net->nlatches; i++) {
	    for (j = 0; j < net->noutputs; j++) {
		if (strcmp(latches[i][0], net->outputs[j]) == 0)
		    break;
	    }
	    if (j < net->noutputs)
		continue;
	    savestring = ALLOC(char, strlen(latches[i][0]) + 1);
	    strcpy(savestring, latches[i][0]);
	    net->outputs[net->noutputs + count] = savestring;
	    count++;
	    if (st_lookup(net->hash, savestring, &node)) {
		if (node->type == BNET_INTERNAL_NODE) {
		    node->type = BNET_OUTPUT_NODE;
		}
	    }
	}
	net->noutputs += count;

	net->inputs = REALLOC(char *, net->inputs,
	    (net->ninputs + net->nlatches) * sizeof(char *));
	for (i = 0; i < net->nlatches; i++) {
	    savestring = ALLOC(char, strlen(latches[i][1]) + 1);
	    strcpy(savestring, latches[i][1]);
	    net->inputs[net->ninputs + i] = savestring;
	}
	net->ninputs += net->nlatches;
    }

    /* Compute fanout counts. For each node in the linked list, fetch
    ** all its fanins using the symbol table, and increment the fanout of
    ** each fanin.
    */
    newnode = net->nodes;
    while (newnode != NULL) {
	BnetNode *auxnd;
	for (i = 0; i < newnode->ninp; i++) {
	    if (!st_lookup(net->hash,newnode->inputs[i],&auxnd)) {
		(void) fprintf(stdout,"%s not driven\n", newnode->inputs[i]);
		goto failure;
	    }
	    auxnd->nfo++;
	}
	newnode = newnode->next;
    }

    if (!bnetSetLevel(net)) goto failure;

    return(net);

failure:
    /* Here we should clean up the mess. */
    (void) fprintf(stdout,"Error in reading network from file.\n");
    return(NULL);

} /* end of Bnet_ReadNetwork */


/**Function********************************************************************

  Synopsis    [Prints a boolean network created by readNetwork.]

  Description [Prints to the standard output a boolean network created
  by Bnet_ReadNetwork. Uses the blif format; this way, one can verify the
  equivalence of the input and the output with, say, sis.]

  SideEffects [None]

  SeeAlso     [Bnet_ReadNetwork]

******************************************************************************/
void
Bnet_PrintNetwork(
  BnetNetwork * net /* boolean network */)
{
    BnetNode *nd;
    BnetTabline *tl;
    int i;

    if (net == NULL) return;

    (void) fprintf(stdout,".model %s\n", net->name);
    (void) fprintf(stdout,".inputs");
    printList(net->inputs,net->npis);
    (void) fprintf(stdout,".outputs");
    printList(net->outputs,net->npos);
    for (i = 0; i < net->nlatches; i++) {
	(void) fprintf(stdout,".latch");
	printList(net->latches[i],3);
    }
    nd = net->nodes;
    while (nd != NULL) {
	if (nd->type != BNET_INPUT_NODE && nd->type != BNET_PRESENT_STATE_NODE) {
	    (void) fprintf(stdout,".names");
	    for (i = 0; i < nd->ninp; i++) {
		(void) fprintf(stdout," %s",nd->inputs[i]);
	    }
	    (void) fprintf(stdout," %s\n",nd->name);
	    tl = nd->f;
	    while (tl != NULL) {
		if (tl->values != NULL) {
		    (void) fprintf(stdout,"%s %d\n",tl->values,
		    1 - nd->polarity);
		} else {
		    (void) fprintf(stdout,"%d\n", 1 - nd->polarity);
		}
		tl = tl->next;
	    }
	}
	nd = nd->next;
    }
    (void) fprintf(stdout,".end\n");

} /* end of Bnet_PrintNetwork */


/**Function********************************************************************

  Synopsis    [Frees a boolean network created by Bnet_ReadNetwork.]

  Description []

  SideEffects [None]

  SeeAlso     [Bnet_ReadNetwork]

******************************************************************************/
void
Bnet_FreeNetwork(
  BnetNetwork * net)
{
    BnetNode *node, *nextnode;
    BnetTabline *line, *nextline;
    int i;

    FREE(net->name);
    /* The input name strings are already pointed by the input nodes.
    ** Here we only need to free the latch names and the array that
    ** points to them.
    */
    for (i = 0; i < net->nlatches; i++) {
	FREE(net->inputs[net->npis + i]);
    }
    FREE(net->inputs);
    /* Free the output name strings and then the array pointing to them.  */
    for (i = 0; i < net->noutputs; i++) {
	FREE(net->outputs[i]);
    }
    FREE(net->outputs);

    for (i = 0; i < net->nlatches; i++) {
	FREE(net->latches[i][0]);
	FREE(net->latches[i][1]);
	FREE(net->latches[i][2]);
	FREE(net->latches[i]);
    }
    if (net->nlatches) FREE(net->latches);
    node = net->nodes;
    while (node != NULL) {
	nextnode = node->next;
	if (node->type != BNET_PRESENT_STATE_NODE)
	    FREE(node->name);
	for (i = 0; i < node->ninp; i++) {
	    FREE(node->inputs[i]);
	}
	if (node->inputs != NULL) {
	    FREE(node->inputs);
	}
	/* Free the function table. */
	line = node->f;
	while (line != NULL) {
	    nextline = line->next;
	    FREE(line->values);
	    FREE(line);
	    line = nextline;
	}
	FREE(node);
	node = nextnode;
    }
    st_free_table(net->hash);
    if (net->slope != NULL) FREE(net->slope);
    FREE(net);

} /* end of Bnet_FreeNetwork */


/**Function********************************************************************

  Synopsis    [Builds the BDD for the function of a node.]

  Description [Builds the BDD for the function of a node and stores a
  pointer to it in the dd field of the node itself. The reference count
  of the BDD is incremented. If params is BNET_LOCAL_DD, then the BDD is
  built in terms of the local inputs to the node; otherwise, if params
  is BNET_GLOBAL_DD, the BDD is built in terms of the network primary
  inputs. To build the global BDD of a node, the BDDs for its local
  inputs must exist. If that is not the case, Bnet_BuildNodeBDD
  recursively builds them. Likewise, to create the local BDD for a node,
  the local inputs must have variables assigned to them. If that is not
  the case, Bnet_BuildNodeBDD recursively assigns variables to nodes.
  Bnet_BuildNodeBDD returns 1 in case of success; 0 otherwise.]

  SideEffects [Sets the dd field of the node.]

  SeeAlso     []

******************************************************************************/
int
Bnet_BuildNodeBDD(
  DdManager * dd /* DD manager */,
  BnetNode * nd /* node of the boolean network */,
  st_table * hash /* symbol table of the boolean network */,
  int  params /* type of DD to be built */,
  int  nodrop /* retain the intermediate node DDs until the end */)
{
    DdNode *func;
    BnetNode *auxnd;
    DdNode *tmp;
    DdNode *prod, *var;
    BnetTabline *line;
    int i;

    if (nd->dd != NULL) return(1);

    if (nd->type == BNET_CONSTANT_NODE) {
	if (nd->f == NULL) { /* constant 0 */
	    func = Cudd_ReadLogicZero(dd);
	} else { /* either constant depending on the polarity */
	    func = Cudd_ReadOne(dd);
	}
	Cudd_Ref(func);
    } else if (nd->type == BNET_INPUT_NODE ||
	       nd->type == BNET_PRESENT_STATE_NODE) {
	if (nd->active == TRUE) { /* a variable is already associated: use it */
	    func = Cudd_ReadVars(dd,nd->var);
	    if (func == NULL) goto failure;
	} else { /* no variable associated: get a new one */
	    func = Cudd_bddNewVar(dd);
	    if (func == NULL) goto failure;
	    nd->var = func->index;
	    nd->active = TRUE;
	}
	Cudd_Ref(func);
    } else if (buildExorBDD(dd,nd,hash,params,nodrop)) {
	func = nd->dd;
    } else if (buildMuxBDD(dd,nd,hash,params,nodrop)) {
	func = nd->dd;
    } else { /* type == BNET_INTERNAL_NODE or BNET_OUTPUT_NODE */
	/* Initialize the sum to logical 0. */
	func = Cudd_ReadLogicZero(dd);
	Cudd_Ref(func);

	/* Build a term for each line of the table and add it to the
	** accumulator (func).
	*/
	line = nd->f;
	while (line != NULL) {
#ifdef BNET_DEBUG
	    (void) fprintf(stdout,"line = %s\n", line->values);
#endif
	    /* Initialize the product to logical 1. */
	    prod = Cudd_ReadOne(dd);
	    Cudd_Ref(prod);
	    /* Scan the table line. */
	    for (i = 0; i < nd->ninp; i++) {
		if (line->values[i] == '-') continue;
		if (!st_lookup(hash,nd->inputs[i],&auxnd)) {
		    goto failure;
		}
		if (params == BNET_LOCAL_DD) {
		    if (auxnd->active == FALSE) {
			if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
			    goto failure;
			}
		    }
		    var = Cudd_ReadVars(dd,auxnd->var);
		    if (var == NULL) goto failure;
		    Cudd_Ref(var);
		    if (line->values[i] == '0') {
			var = Cudd_Not(var);
		    }
		} else { /* params == BNET_GLOBAL_DD */
		    if (auxnd->dd == NULL) {
			if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
			    goto failure;
			}
		    }
		    if (line->values[i] == '1') {
			var = auxnd->dd;
		    } else { /* line->values[i] == '0' */
			var = Cudd_Not(auxnd->dd);
		    }
		}
		tmp = Cudd_bddAnd(dd,prod,var);
		if (tmp == NULL) goto failure;
		Cudd_Ref(tmp);
		Cudd_IterDerefBdd(dd,prod);
		if (params == BNET_LOCAL_DD) {
		    Cudd_IterDerefBdd(dd,var);
		}
		prod = tmp;
	    }
	    tmp = Cudd_bddOr(dd,func,prod);
	    if (tmp == NULL) goto failure;
	    Cudd_Ref(tmp);
	    Cudd_IterDerefBdd(dd,func);
	    Cudd_IterDerefBdd(dd,prod);
	    func = tmp;
	    line = line->next;
	}
	/* Associate a variable to this node if local BDDs are being
	** built. This is done at the end, so that the primary inputs tend
	** to get lower indices.
	*/
	if (params == BNET_LOCAL_DD && nd->active == FALSE) {
	    DdNode *auxfunc = Cudd_bddNewVar(dd);
	    if (auxfunc == NULL) goto failure;
	    Cudd_Ref(auxfunc);
	    nd->var = auxfunc->index;
	    nd->active = TRUE;
	    Cudd_IterDerefBdd(dd,auxfunc);
	}
    }
    if (nd->polarity == 1) {
	nd->dd = Cudd_Not(func);
    } else {
	nd->dd = func;
    }

    if (params == BNET_GLOBAL_DD && nodrop == FALSE) {
	/* Decrease counters for all faninis.
	** When count reaches 0, the DD is freed.
	*/
	for (i = 0; i < nd->ninp; i++) {
	    if (!st_lookup(hash,nd->inputs[i],&auxnd)) {
		goto failure;
	    }
	    auxnd->count--;
	    if (auxnd->count == 0) {
		Cudd_IterDerefBdd(dd,auxnd->dd);
		if (auxnd->type == BNET_INTERNAL_NODE ||
		    auxnd->type == BNET_CONSTANT_NODE) auxnd->dd = NULL;
	    }
	}
    }
    return(1);

failure:
    /* Here we should clean up the mess. */
    return(0);

} /* end of Bnet_BuildNodeBDD */


/**Function********************************************************************

  Synopsis    [Orders the BDD variables by DFS.]

  Description [Orders the BDD variables by DFS.  Returns 1 in case of
  success; 0 otherwise.]

  SideEffects [Uses the visited flags of the nodes.]

  SeeAlso     []

******************************************************************************/
int
Bnet_DfsVariableOrder(
  DdManager * dd,
  BnetNetwork * net)
{
    BnetNode **roots;
    BnetNode *node;
    int nroots;
    int i;

    roots = bnetOrderRoots(net,&nroots);
    if (roots == NULL) return(0);
    for (i = 0; i < nroots; i++) {
	if (!bnetDfsOrder(dd,net,roots[i])) {
	    FREE(roots);
	    return(0);
	}
    }
    /* Clear visited flags. */
    node = net->nodes;
    while (node != NULL) {
	node->visited = 0;
	node = node->next;
    }
    FREE(roots);
    return(1);

} /* end of Bnet_DfsVariableOrder */


/**Function********************************************************************

  Synopsis    [Writes the network BDDs to a file in dot, blif, or daVinci
  format.]

  Description [Writes the network BDDs to a file in dot, blif, or daVinci
  format. If "-" is passed as file name, the BDDs are dumped to the
  standard output. Returns 1 in case of success; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Bnet_bddDump(
  DdManager * dd /* DD manager */,
  BnetNetwork * network /* network whose BDDs should be dumped */,
  char * dfile /* file name */,
  int  dumpFmt /* 0 -> dot */,
  int  reencoded /* whether variables have been reencoded */)
{
    int noutputs;
    FILE *dfp = NULL;
    DdNode **outputs = NULL;
    char **inames = NULL;
    char **onames = NULL;
    char **altnames = NULL;
    BnetNode *node;
    int i;
    int retval = 0; /* 0 -> failure; 1 -> success */

    /* Open dump file. */
    if (strcmp(dfile, "-") == 0) {
	dfp = stdout;
    } else {
	dfp = fopen(dfile,"w");
    }
    if (dfp == NULL) goto endgame;

    /* Initialize data structures. */
    noutputs = network->noutputs;
    outputs = ALLOC(DdNode *,noutputs);
    if (outputs == NULL) goto endgame;
    onames = ALLOC(char *,noutputs);
    if (onames == NULL) goto endgame;
    inames = ALLOC(char *,Cudd_ReadSize(dd));
    if (inames == NULL) goto endgame;

    /* Find outputs and their names. */
    for (i = 0; i < network->nlatches; i++) {
	onames[i] = network->latches[i][0];
	if (!st_lookup(network->hash,network->latches[i][0],&node)) {
	    goto endgame;
	}
	outputs[i] = node->dd;
    }
    for (i = 0; i < network->npos; i++) {
	onames[i + network->nlatches] = network->outputs[i];
	if (!st_lookup(network->hash,network->outputs[i],&node)) {
	    goto endgame;
	}
	outputs[i + network->nlatches] = node->dd;
    }

    /* Find the input names. */
    for (i = 0; i < network->ninputs; i++) {
	if (!st_lookup(network->hash,network->inputs[i],&node)) {
	    goto endgame;
	}
	inames[node->var] = network->inputs[i];
    }
    for (i = 0; i < network->nlatches; i++) {
	if (!st_lookup(network->hash,network->latches[i][1],&node)) {
	    goto endgame;
	}
	inames[node->var] = network->latches[i][1];
    }

    if (reencoded == 1 && dumpFmt == 1) {
	altnames = bnetGenerateNewNames(network->hash,network->ninputs);
	if (altnames == NULL) {
	    retval = 0;
	    goto endgame;
	}
	retval = bnetDumpReencodingLogic(dd,network->name,noutputs,outputs,
		 inames,altnames,onames,dfp);
	for (i = 0; i < network->ninputs; i++) {
	    FREE(altnames[i]);
	}
	FREE(altnames);
	if (retval == 0) goto endgame;
    }

    /* Dump the BDDs. */
    if (dumpFmt == 1) {
	retval = Cudd_DumpBlif(dd,noutputs,outputs,inames,onames,
		 network->name,dfp,0);
    } else if (dumpFmt == 2) {
	retval = Cudd_DumpDaVinci(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 3) {
	retval = Cudd_DumpDDcal(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 4) {
	retval = Cudd_DumpFactoredForm(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 5) {
	retval = Cudd_DumpBlif(dd,noutputs,outputs,inames,onames,
		 network->name,dfp,1);
    } else {
	retval = Cudd_DumpDot(dd,noutputs,outputs,inames,onames,dfp);
    }

endgame:
    if (dfp != stdout && dfp != NULL) {
	if (fclose(dfp) == EOF) retval = 0;
    }
    if (outputs != NULL) FREE(outputs);
    if (onames  != NULL) FREE(onames);
    if (inames  != NULL) FREE(inames);

    return(retval);

} /* end of Bnet_bddDump */


/**Function********************************************************************

  Synopsis    [Writes an array of BDDs to a file in dot, blif, DDcal,
  factored-form, daVinci, or blif-MV format.]

  Description [Writes an array of BDDs to a file in dot, blif, DDcal,
  factored-form, daVinci, or blif-MV format.  The BDDs and their names
  are passed as arguments.  The inputs and their names are taken from
  the network. If "-" is passed as file name, the BDDs are dumped to
  the standard output. Returns 1 in case of success; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Bnet_bddArrayDump(
  DdManager * dd /* DD manager */,
  BnetNetwork * network /* network whose BDDs should be dumped */,
  char * dfile /* file name */,
  DdNode ** outputs /* BDDs to be dumped */,
  char ** onames /* names of the BDDs to be dumped */,
  int  noutputs /* number of BDDs to be dumped */,
  int  dumpFmt /* 0 -> dot */)
{
    FILE *dfp = NULL;
    char **inames = NULL;
    BnetNode *node;
    int i;
    int retval = 0; /* 0 -> failure; 1 -> success */

    /* Open dump file. */
    if (strcmp(dfile, "-") == 0) {
	dfp = stdout;
    } else {
	dfp = fopen(dfile,"w");
    }
    if (dfp == NULL) goto endgame;

    /* Initialize data structures. */
    inames = ALLOC(char *,Cudd_ReadSize(dd));
    if (inames == NULL) goto endgame;
    for (i = 0; i < Cudd_ReadSize(dd); i++) {
	inames[i] = NULL;
    }

    /* Find the input names. */
    for (i = 0; i < network->ninputs; i++) {
	if (!st_lookup(network->hash,network->inputs[i],&node)) {
	    goto endgame;
	}
	inames[node->var] = network->inputs[i];
    }
    for (i = 0; i < network->nlatches; i++) {
	if (!st_lookup(network->hash,network->latches[i][1],&node)) {
	    goto endgame;
	}
	inames[node->var] = network->latches[i][1];
    }

    /* Dump the BDDs. */
    if (dumpFmt == 1) {
	retval = Cudd_DumpBlif(dd,noutputs,outputs,inames,onames,
		 network->name,dfp,0);
    } else if (dumpFmt == 2) {
	retval = Cudd_DumpDaVinci(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 3) {
	retval = Cudd_DumpDDcal(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 4) {
	retval = Cudd_DumpFactoredForm(dd,noutputs,outputs,inames,onames,dfp);
    } else if (dumpFmt == 5) {
	retval = Cudd_DumpBlif(dd,noutputs,outputs,inames,onames,
		 network->name,dfp,1);
    } else {
	retval = Cudd_DumpDot(dd,noutputs,outputs,inames,onames,dfp);
    }

endgame:
    if (dfp != stdout && dfp != NULL) {
	if (fclose(dfp) == EOF) retval = 0;
    }
    if (inames  != NULL) FREE(inames);

    return(retval);

} /* end of Bnet_bddArrayDump */


/**Function********************************************************************

  Synopsis    [Reads the variable order from a file.]

  Description [Reads the variable order from a file.
  Returns 1 if successful; 0 otherwise.]

  SideEffects [The BDDs for the primary inputs and present state variables
  are built.]

  SeeAlso     []

*****************************************************************************/
int
Bnet_ReadOrder(
  DdManager * dd,
  char * ordFile,
  BnetNetwork * net,
  int  locGlob,
  int  nodrop)
{
    FILE *fp;
    st_table *dict;
    int result;
    BnetNode *node;
    char name[MAXLENGTH];

    if (ordFile == NULL) {
	return(0);
    }

    dict = st_init_table(strcmp,st_strhash);
    if (dict == NULL) {
	return(0);
    }

    if ((fp = fopen(ordFile,"r")) == NULL) {
	(void) fprintf(stderr,"Unable to open %s\n",ordFile);
	st_free_table(dict);
	return(0);
    }

    while (!feof(fp)) {
	result = fscanf(fp, "%s", name);
	if (result == EOF) {
	    break;
	} else if (result != 1) {
	    st_free_table(dict);
	    return(0);
	} else if (strlen(name) > MAXLENGTH) {
	    st_free_table(dict);
	    return(0);
	}
	/* There should be a node named "name" in the network. */
	if (!st_lookup(net->hash,name,&node)) {
	    (void) fprintf(stderr,"Unknown name in order file (%s)\n", name);
	    st_free_table(dict);
	    return(0);
	}
	/* A name should not appear more than once in the order. */
	if (st_is_member(dict,name)) {
	    (void) fprintf(stderr,"Duplicate name in order file (%s)\n", name);
	    st_free_table(dict);
	    return(0);
	}
	/* The name should correspond to a primary input or present state. */
	if (node->type != BNET_INPUT_NODE &&
	    node->type != BNET_PRESENT_STATE_NODE) {
	    (void) fprintf(stderr,"%s has the wrong type (%d)\n", name,
			   node->type);
	    st_free_table(dict);
	    return(0);
	}
	/* Insert in table. Use node->name rather than name, because the
	** latter gets overwritten.
	*/
	if (st_insert(dict,node->name,NULL) == ST_OUT_OF_MEM) {
	    (void) fprintf(stderr,"Out of memory in Bnet_ReadOrder\n");
	    st_free_table(dict);
	    return(0);
	}
	result = Bnet_BuildNodeBDD(dd,node,net->hash,locGlob,nodrop);
	if (result == 0) {
	    (void) fprintf(stderr,"Construction of BDD failed\n");
	    st_free_table(dict);
	    return(0);
	}
    } /* while (!feof(fp)) */
    result = fclose(fp);
    if (result == EOF) {
	(void) fprintf(stderr,"Error closing order file %s\n", ordFile);
	st_free_table(dict);
	return(0);
    }

    /* The number of names in the order file should match exactly the
    ** number of primary inputs and present states.
    */
    if (st_count(dict) != net->ninputs) {
	(void) fprintf(stderr,"Order incomplete: %d names instead of %d\n",
		       st_count(dict), net->ninputs);
	st_free_table(dict);
	return(0);
    }

    st_free_table(dict);
    return(1);

} /* end of Bnet_ReadOrder */


/**Function********************************************************************

  Synopsis    [Prints the order of the DD variables of a network.]

  Description [Prints the order of the DD variables of a network.
  Only primary inputs and present states are printed.
  Returns 1 if successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

*****************************************************************************/
int
Bnet_PrintOrder(
  BnetNetwork * net,
  DdManager *dd)
{
    char **names;		/* array used to print variable orders */
    int	level;			/* position of a variable in current order */
    BnetNode *node;		/* auxiliary pointer to network node */
    int i,j;
    int retval;
    int nvars;

    nvars = Cudd_ReadSize(dd);
    names = ALLOC(char *, nvars);
    if (names == NULL) return(0);
    for (i = 0; i < nvars; i++) {
	names[i] = NULL;
    }
    for (i = 0; i < net->npis; i++) {
	if (!st_lookup(net->hash,net->inputs[i],&node)) {
	    FREE(names);
	    return(0);
	}
	if (node->dd == NULL) {
	    FREE(names);
	    return(0);
	}
	level = Cudd_ReadPerm(dd,node->var);
	names[level] = node->name;
    }
    for (i = 0; i < net->nlatches; i++) {
	if (!st_lookup(net->hash,net->latches[i][1],&node)) {
	    FREE(names);
	    return(0);
	}
	if (node->dd == NULL) {
	    FREE(names);
	    return(0);
	}
	level = Cudd_ReadPerm(dd,node->var);
	names[level] = node->name;
    }
    for (i = 0, j = 0; i < nvars; i++) {
	if (names[i] == NULL) continue;
	if ((j%8 == 0)&&j) {
	    retval = printf("\n");
	    if (retval == EOF) {
		FREE(names);
		return(0);
	    }
	}
	retval = printf("%s ",names[i]);
	if (retval == EOF) {
	    FREE(names);
	    return(0);
	}
	j++;
    }
    FREE(names);
    retval = printf("\n");
    if (retval == EOF) {
	return(0);
    }
    return(1);

} /* end of Bnet_PrintOrder */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Reads a string from a file.]

  Description [Reads a string from a file. The string can be MAXLENGTH-1
  characters at most. readString allocates memory to hold the string and
  returns a pointer to the result if successful. It returns NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     [readList]

******************************************************************************/
static char *
readString(
  FILE * fp /* pointer to the file from which the string is read */)
{
    char *savestring;
    int length;

    while (!CurPos) {
	if (!fgets(BuffLine, MAXLENGTH, fp))
	    return(NULL);
	BuffLine[strlen(BuffLine) - 1] = '\0';
	CurPos = strtok(BuffLine, " \t");
	if (CurPos && CurPos[0] == '#') CurPos = (char *)NULL;
    }
    length = strlen(CurPos);
    savestring = ALLOC(char,length+1);
    if (savestring == NULL)
	return(NULL);
    strcpy(savestring,CurPos);
    CurPos = strtok(NULL, " \t");
    return(savestring);

} /* end of readString */


/**Function********************************************************************

  Synopsis    [Reads a list of strings from a file.]

  Description [Reads a list of strings from a line of a file.
  The strings are sequences of characters separated by spaces or tabs.
  The total length of the list, white space included, must not exceed
  MAXLENGTH-1 characters.  readList allocates memory for the strings and
  creates an array of pointers to the individual lists. Only two pieces
  of memory are allocated by readList: One to hold all the strings,
  and one to hold the pointers to them. Therefore, when freeing the
  memory allocated by readList, only the pointer to the list of
  pointers, and the pointer to the beginning of the first string should
  be freed. readList returns the pointer to the list of pointers if
  successful; NULL otherwise.]

  SideEffects [n is set to the number of strings in the list.]

  SeeAlso     [readString printList]

******************************************************************************/
static char **
readList(
  FILE * fp /* pointer to the file from which the list is read */,
  int * n /* on return, number of strings in the list */)
{
    char	*savestring;
    int		length;
    char	*stack[8192];
    char	**list;
    int		i, count = 0;

    while (CurPos) {
	if (strcmp(CurPos, "\\") == 0) {
	    CurPos = (char *)NULL;
	    while (!CurPos) {
		if (!fgets(BuffLine, MAXLENGTH, fp)) return(NULL);
		BuffLine[strlen(BuffLine) - 1] = '\0';
		CurPos = strtok(BuffLine, " \t");
	    }
	}
	length = strlen(CurPos);
	savestring = ALLOC(char,length+1);
	if (savestring == NULL) return(NULL);
	strcpy(savestring,CurPos);
	stack[count] = savestring;
	count++;
	CurPos = strtok(NULL, " \t");
    }
    list = ALLOC(char *, count);
    for (i = 0; i < count; i++)
	list[i] = stack[i];
    *n = count;
    return(list);

} /* end of readList */


/**Function********************************************************************

  Synopsis    [Prints a list of strings to the standard output.]

  Description [Prints a list of strings to the standard output. The list
  is in the format created by readList.]

  SideEffects [None]

  SeeAlso     [readList Bnet_PrintNetwork]

******************************************************************************/
static void
printList(
  char ** list /* list of pointers to strings */,
  int  n /* length of the list */)
{
    int i;

    for (i = 0; i < n; i++) {
	(void) fprintf(stdout," %s",list[i]);
    }
    (void) fprintf(stdout,"\n");

} /* end of printList */


/**Function********************************************************************

  Synopsis    [Generates names not currently in a symbol table.]

  Description [Generates n names not currently in the symbol table hash.
  The pointer to the symbol table may be NULL, in which case no test is
  made. The names generated by the procedure are unique. So, if there is
  no possibility of conflict with pre-existing names, NULL can be passed
  for the hash table.  Returns an array of names if succesful; NULL
  otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static char **
bnetGenerateNewNames(
  st_table * hash /* table of existing names (or NULL) */,
  int  n /* number of names to be generated */)
{
    char **list;
    char name[256];
    int i;

    if (n < 1) return(NULL);

    list = ALLOC(char *,n);
    if (list == NULL) return(NULL);
    for (i = 0; i < n; i++) {
	do {
	    sprintf(name, "var%d", newNameNumber);
	    newNameNumber++;
	} while (hash != NULL && st_is_member(hash,name));
	list[i] = util_strsav(name);
    }

    return(list);

} /* bnetGenerateNewNames */


/**Function********************************************************************

  Synopsis    [Writes blif for the reencoding logic.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
bnetDumpReencodingLogic(
  DdManager * dd /* DD manager */,
  char * mname /* model name */,
  int  noutputs /* number of outputs */,
  DdNode ** outputs /* array of network outputs */,
  char ** inames /* array of network input names */,
  char ** altnames /* array of names of reencoded inputs */,
  char ** onames /* array of network output names */,
  FILE * fp /* file pointer */)
{
    int i;
    int retval;
    int nvars = Cudd_ReadSize(dd);
    int *support = NULL;

    support = bnetFindVectorSupport(dd,outputs,noutputs);
    if (support == NULL) return(0);

    /* Write the header (.model .inputs .outputs). */
    retval = fprintf(fp,".model %s.global\n.inputs",mname);
    if (retval == EOF) goto failure;

    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	retval = fprintf(fp," %s", inames[i]);
	if (retval == EOF) goto failure;
    }

    /* Write the .output line. */
    retval = fprintf(fp,"\n.outputs");
    if (retval == EOF) goto failure;
    for (i = 0; i < noutputs; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	retval = fprintf(fp," %s", onames[i]);
	if (retval == EOF) goto failure;
    }
    retval = fprintf(fp,"\n");
    if (retval == EOF) goto failure;

    /* Instantiate main subcircuit. */
    retval = fprintf(fp,"\n.subckt %s", mname);
    if (retval == EOF) goto failure;
    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	if (support[i] == 1) {
	    retval = fprintf(fp," %s=%s", inames[i], altnames[i]);
	    if (retval == EOF) goto failure;
	}
    }
    for (i = 0; i < noutputs; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	retval = fprintf(fp," %s=%s", onames[i], onames[i]);
	if (retval == EOF) goto failure;
    }
    retval = fprintf(fp,"\n");
    if (retval == EOF) goto failure;

    /* Instantiate reencoding subcircuit. */
    retval = fprintf(fp,"\n.subckt %s.reencode",mname);
    if (retval == EOF) goto failure;
    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	retval = fprintf(fp," %s=%s", inames[i], inames[i]);
	if (retval == EOF) goto failure;
    }
    retval = fprintf(fp," \\\n");
    if (retval == EOF) goto failure;
    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	if (support[i] == 1) {
	    retval = fprintf(fp," %s=%s", altnames[i],altnames[i]);
	    if (retval == EOF) goto failure;
	}
    }
    retval = fprintf(fp,"\n");
    if (retval == EOF) goto failure;

    /* Write trailer. */
    retval = fprintf(fp,".end\n\n");
    if (retval == EOF) goto failure;

    /* Write reencoding subcircuit. */
    retval = bnetBlifWriteReencode(dd,mname,inames,altnames,support,fp);
    if (retval == EOF) goto failure;

    FREE(support);
    return(1);

failure:
    if (support != NULL) FREE(support);
    return(0);

} /* end of bnetDumpReencodingLogic */


/**Function********************************************************************

  Synopsis    [Writes blif for the truth table of an n-input xnor.]

  Description [Writes blif for the truth table of an n-input
  xnor. Returns 1 if successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
#if 0
static int
bnetBlifXnorTable(
  FILE * fp /* file pointer */,
  int  n /* number of inputs */)
{
    int power;	/* 2 to the power n */
    int i,j,k;
    int nzeroes;
    int retval;
    char *line;

    line = ALLOC(char,n+1);
    if (line == NULL) return(0);
    line[n] = '\0';

    for (i = 0, power = 1; i < n; i++) {
	power *= 2;
    }

    for (i = 0; i < power; i++) {
	k = i;
	nzeroes = 0;
	for (j = 0; j < n; j++) {
	    if (k & 1) {
		line[j] = '1';
	    } else {
		line[j] = '0';
		nzeroes++;
	    }
	    k >>= 1;
	}
	if ((nzeroes & 1) == 0) {
	    retval = fprintf(fp,"%s 1\n",line);
	    if (retval == 0) return(0);
	}
    }
    return(1);

} /* end of bnetBlifXnorTable */
#endif


/**Function********************************************************************

  Synopsis    [Writes blif for the reencoding logic.]

  Description [Writes blif for the reencoding logic. Exclusive NORs
  with more than two inputs are decomposed into cascaded two-input
  gates. Returns 1 if successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
bnetBlifWriteReencode(
  DdManager * dd,
  char * mname,
  char ** inames,
  char ** altnames,
  int * support,
  FILE * fp)
{
    int retval;
    int nvars = Cudd_ReadSize(dd);
    int i,j;
    int ninp;

    /* Write the header (.model .inputs .outputs). */
    retval = fprintf(fp,".model %s.reencode\n.inputs",mname);
    if (retval == EOF) return(0);

    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	retval = fprintf(fp," %s", inames[i]);
	if (retval == EOF) goto failure;
    }

    /* Write the .output line. */
    retval = fprintf(fp,"\n.outputs");
    if (retval == EOF) goto failure;
    for (i = 0; i < nvars; i++) {
	if ((i%8 == 0)&&i) {
	    retval = fprintf(fp," \\\n");
	    if (retval == EOF) goto failure;
	}
	if (support[i] == 1) {
	    retval = fprintf(fp," %s", altnames[i]);
	    if (retval == EOF) goto failure;
	}
    }
    retval = fprintf(fp,"\n");
    if (retval == EOF) goto failure;

    /* Instantiate exclusive nors. */
    for (i = 0; i < nvars; i++) {
	char *in1 = NULL;
	char *in2 = NULL;
	char **oname;
	if (support[i] == 0) continue;
	ninp = 0;
	for (j = 0; j < nvars; j++) {
	    if (Cudd_ReadLinear(dd,i,j)) {
		switch (ninp) {
		case 0:
		    in1 = inames[j];
		    ninp++;
		    break;
		case 1:
		    in2 = inames[j];
		    ninp++;
		    break;
		case 2:
		    oname = bnetGenerateNewNames(NULL,1);
		    retval = fprintf(fp,".names %s %s %s\n11 1\n00 1\n",
			     in1, in2, oname[0]);
		    if (retval == EOF) goto failure;
		    in1 = oname[0];
		    in2 = inames[j];
		    FREE(oname);
		    break;
		default:
		    goto failure;
		}
	    }
	}
	switch (ninp) {
	case 1:
	    retval = fprintf(fp,".names %s %s\n1 1\n", in1, altnames[i]);
	    if (retval == EOF) goto failure;
	    break;
	case 2:
	    retval = fprintf(fp,".names %s %s %s\n11 1\n00 1\n",
		     in1, in2, altnames[i]);
	    if (retval == EOF) goto failure;
	    break;
	default:
	    goto failure;
	}
    }

    /* Write trailer. */
    retval = fprintf(fp,"\n.end\n\n");
    if (retval == EOF) goto failure;

    return(1);

failure:
    return(0);

} /* end of bnetBlifWriteReencode */


/**Function********************************************************************

  Synopsis    [Finds the support of a list of DDs.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int *
bnetFindVectorSupport(
  DdManager * dd,
  DdNode ** list,
  int  n)
{
    DdNode	*support = NULL;
    DdNode	*scan;
    int		*array = NULL;
    int		nvars = Cudd_ReadSize(dd);
    int		i;

    /* Build an array with the support of the functions in list. */
    array = ALLOC(int,nvars);
    if (array == NULL) return(NULL);
    for (i = 0; i < nvars; i++) {
	array[i] = 0;
    }

    /* Take the union of the supports of each output function. */
    for (i = 0; i < n; i++) {
	support = Cudd_Support(dd,list[i]);
	if (support == NULL) {
	    FREE(array);
	    return(NULL);
	}
	Cudd_Ref(support);
	scan = support;
	while (!Cudd_IsConstant(scan)) {
	    array[scan->index] = 1;
	    scan = Cudd_T(scan);
	}
	Cudd_IterDerefBdd(dd,support);
    }

    return(array);

} /* end of bnetFindVectorSupport */


/**Function********************************************************************

  Synopsis    [Builds BDD for a XOR function.]

  Description [Checks whether a function is a XOR with 2 or 3 inputs. If so,
  it builds the BDD. Returns 1 if the BDD has been built; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
buildExorBDD(
  DdManager * dd,
  BnetNode * nd,
  st_table * hash,
  int  params,
  int  nodrop)
{
    int check[8];
    int i;
    int nlines;
    BnetTabline *line;
    DdNode *func, *var, *tmp;
    BnetNode *auxnd;

    if (nd->ninp < 2 || nd->ninp > 3) return(0);

    nlines = 1 << (nd->ninp - 1);
    for (i = 0; i < 8; i++) check[i] = 0;
    line = nd->f;
    while (line != NULL) {
	int num = 0;
	int count = 0;
	nlines--;
	for (i = 0; i < nd->ninp; i++) {
	    num <<= 1;
	    if (line->values[i] == '-') {
		return(0);
	    } else if (line->values[i] == '1') {
		count++;
		num++;
	    }
	}
	if ((count & 1) == 0) return(0);
	if (check[num]) return(0);
	line = line->next;
    }
    if (nlines != 0) return(0);

    /* Initialize the exclusive sum to logical 0. */
    func = Cudd_ReadLogicZero(dd);
    Cudd_Ref(func);

    /* Scan the inputs. */
    for (i = 0; i < nd->ninp; i++) {
	if (!st_lookup(hash, nd->inputs[i], &auxnd)) {
	    goto failure;
	}
	if (params == BNET_LOCAL_DD) {
	    if (auxnd->active == FALSE) {
		if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		    goto failure;
		}
	    }
	    var = Cudd_ReadVars(dd,auxnd->var);
	    if (var == NULL) goto failure;
	    Cudd_Ref(var);
	} else { /* params == BNET_GLOBAL_DD */
	    if (auxnd->dd == NULL) {
		if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		    goto failure;
		}
	    }
	    var = auxnd->dd;
	}
	tmp = Cudd_bddXor(dd,func,var);
	if (tmp == NULL) goto failure;
	Cudd_Ref(tmp);
	Cudd_IterDerefBdd(dd,func);
	if (params == BNET_LOCAL_DD) {
	    Cudd_IterDerefBdd(dd,var);
	}
	func = tmp;
    }
    nd->dd = func;

    /* Associate a variable to this node if local BDDs are being
    ** built. This is done at the end, so that the primary inputs tend
    ** to get lower indices.
    */
    if (params == BNET_LOCAL_DD && nd->active == FALSE) {
	DdNode *auxfunc = Cudd_bddNewVar(dd);
	if (auxfunc == NULL) goto failure;
	Cudd_Ref(auxfunc);
	nd->var = auxfunc->index;
	nd->active = TRUE;
	Cudd_IterDerefBdd(dd,auxfunc);
    }

    return(1);
failure:
    return(0);

} /* end of buildExorBDD */


/**Function********************************************************************

  Synopsis    [Builds BDD for a multiplexer.]

  Description [Checks whether a function is a 2-to-1 multiplexer. If so,
  it builds the BDD. Returns 1 if the BDD has been built; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static int
buildMuxBDD(
  DdManager * dd,
  BnetNode * nd,
  st_table * hash,
  int  params,
  int  nodrop)
{
    BnetTabline *line;
    char *values[2];
    int mux[2];
    int phase[2];
    int j;
    int nlines = 0;
    int controlC = -1;
    int controlR = -1;
    DdNode *func, *f, *g, *h;
    BnetNode *auxnd;

    if (nd->ninp != 3) return(0);

    for (line = nd->f; line != NULL; line = line->next) {
	int dc = 0;
	if (nlines > 1) return(0);
	values[nlines] = line->values;
	for (j = 0; j < 3; j++) {
	    if (values[nlines][j] == '-') {
		if (dc) return(0);
		dc = 1;
	    }
	}
	if (!dc) return(0);
	nlines++;
    }
    /* At this point we know we have:
    **   3 inputs
    **   2 lines
    **   1 dash in each line
    ** If the two dashes are not in the same column, then there is
    ** exaclty one column without dashes: the control column.
    */
    for (j = 0; j < 3; j++) {
	if (values[0][j] == '-' && values[1][j] == '-') return(0);
	if (values[0][j] != '-' && values[1][j] != '-') {
	    if (values[0][j] == values[1][j]) return(0);
	    controlC = j;
	    controlR = values[0][j] == '0';
	}
    }
    assert(controlC != -1 && controlR != -1);
    /* At this point we know that there is indeed no column with two
    ** dashes. The control column has been identified, and we know that
    ** its two elelments are different. */
    for (j = 0; j < 3; j++) {
	if (j == controlC) continue;
	if (values[controlR][j] == '1') {
	    mux[0] = j;
	    phase[0] = 0;
	} else if (values[controlR][j] == '0') {
	    mux[0] = j;
	    phase[0] = 1;
	} else if (values[1-controlR][j] == '1') {
	    mux[1] = j;
	    phase[1] = 0;
	} else if (values[1-controlR][j] == '0') {
	    mux[1] = j;
	    phase[1] = 1;
	}
    }

    /* Get the inputs. */
    if (!st_lookup(hash, nd->inputs[controlC], &auxnd)) {
	goto failure;
    }
    if (params == BNET_LOCAL_DD) {
	if (auxnd->active == FALSE) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	f = Cudd_ReadVars(dd,auxnd->var);
	if (f == NULL) goto failure;
	Cudd_Ref(f);
    } else { /* params == BNET_GLOBAL_DD */
	if (auxnd->dd == NULL) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	f = auxnd->dd;
    }
    if (!st_lookup(hash, nd->inputs[mux[0]], &auxnd)) {
	goto failure;
    }
    if (params == BNET_LOCAL_DD) {
	if (auxnd->active == FALSE) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	g = Cudd_ReadVars(dd,auxnd->var);
	if (g == NULL) goto failure;
	Cudd_Ref(g);
    } else { /* params == BNET_GLOBAL_DD */
	if (auxnd->dd == NULL) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	g = auxnd->dd;
    }
    g = Cudd_NotCond(g,phase[0]);
    if (!st_lookup(hash, nd->inputs[mux[1]], &auxnd)) {
	goto failure;
    }
    if (params == BNET_LOCAL_DD) {
	if (auxnd->active == FALSE) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	h = Cudd_ReadVars(dd,auxnd->var);
	if (h == NULL) goto failure;
	Cudd_Ref(h);
    } else { /* params == BNET_GLOBAL_DD */
	if (auxnd->dd == NULL) {
	    if (!Bnet_BuildNodeBDD(dd,auxnd,hash,params,nodrop)) {
		goto failure;
	    }
	}
	h = auxnd->dd;
    }
    h = Cudd_NotCond(h,phase[1]);
    func = Cudd_bddIte(dd,f,g,h);
    if (func == NULL) goto failure;
    Cudd_Ref(func);
    if (params == BNET_LOCAL_DD) {
	Cudd_IterDerefBdd(dd,f);
	Cudd_IterDerefBdd(dd,g);
	Cudd_IterDerefBdd(dd,h);
    }
    nd->dd = func;

    /* Associate a variable to this node if local BDDs are being
    ** built. This is done at the end, so that the primary inputs tend
    ** to get lower indices.
    */
    if (params == BNET_LOCAL_DD && nd->active == FALSE) {
	DdNode *auxfunc = Cudd_bddNewVar(dd);
	if (auxfunc == NULL) goto failure;
	Cudd_Ref(auxfunc);
	nd->var = auxfunc->index;
	nd->active = TRUE;
	Cudd_IterDerefBdd(dd,auxfunc);
    }

    return(1);
failure:
    return(0);

} /* end of buildExorBDD */


/**Function********************************************************************

  Synopsis    [Sets the level of each node.]

  Description [Sets the level of each node. Returns 1 if successful; 0
  otherwise.]

  SideEffects [Changes the level and visited fields of the nodes it
  visits.]

  SeeAlso     [bnetLevelDFS]

******************************************************************************/
static int
bnetSetLevel(
  BnetNetwork * net)
{
    BnetNode *node;

    /* Recursively visit nodes. This is pretty inefficient, because we
    ** visit all nodes in this loop, and most of them in the recursive
    ** calls to bnetLevelDFS. However, this approach guarantees that
    ** all nodes will be reached ven if there are dangling outputs. */
    node = net->nodes;
    while (node != NULL) {
	if (!bnetLevelDFS(net,node)) return(0);
	node = node->next;
    }

    /* Clear visited flags. */
    node = net->nodes;
    while (node != NULL) {
	node->visited = 0;
	node = node->next;
    }
    return(1);

} /* end of bnetSetLevel */


/**Function********************************************************************

  Synopsis    [Does a DFS from a node setting the level field.]

  Description [Does a DFS from a node setting the level field. Returns
  1 if successful; 0 otherwise.]

  SideEffects [Changes the level and visited fields of the nodes it
  visits.]

  SeeAlso     [bnetSetLevel]

******************************************************************************/
static int
bnetLevelDFS(
  BnetNetwork * net,
  BnetNode * node)
{
    int i;
    BnetNode *auxnd;

    if (node->visited == 1) {
	return(1);
    }

    node->visited = 1;

    /* Graphical sources have level 0.  This is the final value if the
    ** node has no fan-ins. Otherwise the successive loop will
    ** increase the level. */
    node->level = 0;
    for (i = 0; i < node->ninp; i++) {
	if (!st_lookup(net->hash, node->inputs[i], &auxnd)) {
	    return(0);
	}
	if (!bnetLevelDFS(net,auxnd)) {
	    return(0);
	}
	if (auxnd->level >= node->level) node->level = 1 + auxnd->level;
    }
    return(1);

} /* end of bnetLevelDFS */


/**Function********************************************************************

  Synopsis    [Orders network roots for variable ordering.]

  Description [Orders network roots for variable ordering. Returns
  an array with the ordered outputs and next state variables if
  successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
static BnetNode **
bnetOrderRoots(
  BnetNetwork * net,
  int * nroots)
{
    int i, noutputs;
    BnetNode *node;
    BnetNode **nodes = NULL;

    /* Initialize data structures. */
    noutputs = net->noutputs;
    nodes = ALLOC(BnetNode *, noutputs);
    if (nodes == NULL) goto endgame;

    /* Find output names and levels. */
    for (i = 0; i < net->noutputs; i++) {
	if (!st_lookup(net->hash,net->outputs[i],&node)) {
	    goto endgame;
	}
	nodes[i] = node;
    }

    qsort((void *)nodes, noutputs, sizeof(BnetNode *),
	  (DD_QSFP)bnetLevelCompare);
    *nroots = noutputs;
    return(nodes);

endgame:
    if (nodes != NULL) FREE(nodes);
    return(NULL);

} /* end of bnetOrderRoots */


/**Function********************************************************************

  Synopsis    [Comparison function used by qsort.]

  Description [Comparison function used by qsort to order the
  variables according to the number of keys in the subtables.
  Returns the difference in number of keys between the two
  variables being compared.]

  SideEffects [None]

******************************************************************************/
static int
bnetLevelCompare(
  BnetNode ** x,
  BnetNode ** y)
{
    return((*y)->level - (*x)->level);

} /* end of bnetLevelCompare */


/**Function********************************************************************

  Synopsis    [Does a DFS from a node ordering the inputs.]

  Description [Does a DFS from a node ordering the inputs. Returns
  1 if successful; 0 otherwise.]

  SideEffects [Changes visited fields of the nodes it visits.]

  SeeAlso     [Bnet_DfsVariableOrder]

******************************************************************************/
static int
bnetDfsOrder(
  DdManager * dd,
  BnetNetwork * net,
  BnetNode * node)
{
    int i;
    BnetNode *auxnd;
    BnetNode **fanins;

    if (node->visited == 1) {
	return(1);
    }

    node->visited = 1;
    if (node->type == BNET_INPUT_NODE ||
	node->type == BNET_PRESENT_STATE_NODE) {
	node->dd = Cudd_bddNewVar(dd);
	if (node->dd == NULL) return(0);
	Cudd_Ref(node->dd);
	node->active = TRUE;
	node->var = node->dd->index;
	return(1);
    }

    fanins = ALLOC(BnetNode *, node->ninp);
    if (fanins == NULL) return(0);

    for (i = 0; i < node->ninp; i++) {
	if (!st_lookup(net->hash, node->inputs[i], &auxnd)) {
	    FREE(fanins);
	    return(0);
	}
	fanins[i] = auxnd;
    }

    qsort((void *)fanins, node->ninp, sizeof(BnetNode *),
	  (DD_QSFP)bnetLevelCompare);
    for (i = 0; i < node->ninp; i++) {
	/* for (i = node->ninp - 1; i >= 0; i--) { */
	int res = bnetDfsOrder(dd,net,fanins[i]);
	if (res == 0) {
	    FREE(fanins);
	    return(0);
	}
    }
    FREE(fanins);
    return(1);

} /* end of bnetLevelDFS */
