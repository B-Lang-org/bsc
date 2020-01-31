/**CFile***********************************************************************

  FileName    [ntrHeap.c]

  PackageName [ntr]

  Synopsis    [Functions for heap-based priority queue.]

  Description [The functions in this file manage a priority queue implemented
  as a heap. The first element of the heap is the one with the smallest key.
  Refer to Chapter 7 of Cormen, Leiserson, and Rivest for the theory.]

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
static char rcsid[] UTIL_UNUSED = "$Id: ntrHeap.c,v 1.6 2012/02/05 01:53:01 fabio Exp fabio $";
#endif

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

#define PARENT(i)	(((i)-1)>>1)
#define RIGHT(i)	(((i)+1)<<1)
#define LEFT(i)		(((i)<<1)|1)
#define ITEM(p,i)	((p)[i].item)
#define KEY(p,i)	((p)[i].key)

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

static void ntrHeapify (NtrHeap *heap, int i);
static int ntrHeapResize (NtrHeap *heap);

/**AutomaticEnd***************************************************************/

/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Initializes a priority queue.]

  Description [Initializes a priority queue. Returns a pointer to the heap
  if successful; NULL otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_FreeHeap]

******************************************************************************/
NtrHeap *
Ntr_InitHeap(
  int size)
{
    NtrHeap *heap;

    heap = ALLOC(NtrHeap,1);
    if (heap == NULL) return(NULL);
    heap->size = size;
    heap->nslots = 0;
    heap->slots = ALLOC(NtrHeapSlot,size);
    if (heap->slots == NULL) {
	FREE(heap);
	return(NULL);
    }
    return(heap);

} /* end of Ntr_InitHeap */


/**Function********************************************************************

  Synopsis    [Frees a priority queue.]

  Description []

  SideEffects [None]

  SeeAlso     [Ntr_InitHeap]

******************************************************************************/
void
Ntr_FreeHeap(
  NtrHeap *heap)
{
    FREE(heap->slots);
    FREE(heap);
    return;

} /* end of Ntr_FreeHeap */


/**Function********************************************************************

  Synopsis    [Inserts an item in a priority queue.]

  Description [Inserts an item in a priority queue. Returns 1 if successful;
  0 otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_HeapExtractMin]

******************************************************************************/
int
Ntr_HeapInsert(
  NtrHeap *heap,
  void *item,
  int key)
{
    NtrHeapSlot *slots;
    int i = heap->nslots;

    if (i == heap->size && !ntrHeapResize(heap)) return(0);
    slots = heap->slots;
    heap->nslots++;
    while (i > 0 && KEY(slots,PARENT(i)) > key) {
	ITEM(slots,i) = ITEM(slots,PARENT(i));
	KEY(slots,i) = KEY(slots,PARENT(i));
	i = PARENT(i);
    }
    ITEM(slots,i) = item;
    KEY(slots,i) = key;
    return(1);

} /* end of Ntr_HeapInsert */


/**Function********************************************************************

  Synopsis    [Extracts the element with the minimum key from a priority
  queue.]

  Description [Extracts the element with the minimum key from a priority
  queue. Returns 1 if successful; 0 otherwise.]

  SideEffects [The minimum key and the associated item are returned as
  side effects.]

  SeeAlso     [Ntr_HeapInsert]

******************************************************************************/
int
Ntr_HeapExtractMin(
  NtrHeap *heap,
  void *item,
  int *key)
{
    NtrHeapSlot *slots = heap->slots;

    if (heap->nslots == 0) return(0);
    *(void **)item = ITEM(slots,0);
    *key = KEY(slots,0);
    heap->nslots--;
    ITEM(slots,0) = ITEM(slots,heap->nslots);
    KEY(slots,0) = KEY(slots,heap->nslots);
    ntrHeapify(heap,0);

    return(1);

} /* end of Ntr_HeapExtractMin */


/**Function********************************************************************

  Synopsis    [Returns the number of items in a priority queue.]

  Description []

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Ntr_HeapCount(
  NtrHeap *heap)
{
    return(heap->nslots);

} /* end of Ntr_HeapCount */


/**Function********************************************************************

  Synopsis    [Clones a priority queue.]

  Description []

  SideEffects [None]

  SeeAlso     [Ntr_InitHeap]

******************************************************************************/
NtrHeap *
Ntr_HeapClone(
  NtrHeap *source)
{
    NtrHeap *dest;
    int i;
    int nslots = source->nslots;
    NtrHeapSlot *sslots = source->slots;
    NtrHeapSlot *dslots;

    dest = Ntr_InitHeap(source->size);
    if (dest == NULL) return(NULL);
    dest->nslots = nslots;
    dslots = dest->slots;
    for (i = 0; i < nslots; i++) {
	KEY(dslots,i) = KEY(sslots,i);
	ITEM(dslots,i) = ITEM(sslots,i);
    }
    return(dest);

} /* end of Ntr_HeapClone */


/**Function********************************************************************

  Synopsis    [Tests the heap property of a priority queue.]

  Description [Tests the heap property of a priority queue. Returns 1 if
  Successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     []

******************************************************************************/
int
Ntr_TestHeap(
  NtrHeap *heap,
  int i)
{
    NtrHeapSlot *slots = heap->slots;
    int nslots = heap->nslots;

    if (i > 0 && KEY(slots,i) < KEY(slots,PARENT(i)))
	return(0);
    if (LEFT(i) < nslots) {
	if (!Ntr_TestHeap(heap,LEFT(i)))
	    return(0);
    }
    if (RIGHT(i) < nslots) {
	if (!Ntr_TestHeap(heap,RIGHT(i)))
	    return(0);
    }
    return(1);

} /* end of Ntr_TestHeap */


/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Maintains the heap property of a priority queue.]

  Description []

  SideEffects [None]

  SeeAlso     [Ntr_HeapExtractMin]

******************************************************************************/
static void
ntrHeapify(
  NtrHeap *heap,
  int i)
{
    int smallest;
    int left = LEFT(i);
    int right = RIGHT(i);
    int nslots = heap->nslots;
    NtrHeapSlot *slots = heap->slots;
    int key = KEY(slots,i);

    if (left < nslots && KEY(slots,left) < key) {
	smallest = left;
    } else {
	smallest = i;
    }
    if (right < nslots && KEY(slots,right) < KEY(slots,smallest)) {
	smallest = right;
    }
    if (smallest != i) {
	void *item = ITEM(slots,i);
	KEY(slots,i) = KEY(slots,smallest);
	ITEM(slots,i) = ITEM(slots,smallest);
	KEY(slots,smallest) = key;
	ITEM(slots,smallest) = item;
	ntrHeapify(heap,smallest);
    }

    return;

} /* end of ntrHeapify */


/**Function********************************************************************

  Synopsis    [Resizes a priority queue.]

  Description [Resizes a priority queue by doubling the number of
  available slots.  Returns 1 if successful; 0 otherwise.]

  SideEffects [None]

  SeeAlso     [Ntr_HeapInsert]

******************************************************************************/
static int
ntrHeapResize(
  NtrHeap *heap)
{
  int oldlength = heap->size;
  int newlength = 2 * oldlength;
  NtrHeapSlot *oldslots = heap->slots;
  NtrHeapSlot *newslots = REALLOC(NtrHeapSlot, oldslots, newlength);
  if (newslots == NULL) return 0;
  heap->size = newlength;
  heap->slots = newslots;
  assert(Ntr_TestHeap(heap, 0));
  return 1;

} /* end of ntrHeapResize */
