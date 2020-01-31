/**CFile***********************************************************************

  FileName    [cuddPwPt.c]

  PackageName [cudd]

  Synopsis    [Emulation functions for the power package in SIS.]

  Description [This file contains functions that are necessary for the
  power package in SIS. This package directly calls a few functions of
  the CMU BDD package. Therefore, functions with identical names and
  equivalent functionality are provided here.
	External procedures included in this file:
		<ul>
		<li> cmu_bdd_zero()
		<li> cmu_bdd_one()
		<li> cmu_bdd_if_index()
		</ul>
	Internal procedures included in this module:
		<ul>
		<li> 
		</ul>]

  Author      [Fabio Somenzi]

  Copyright   [This file was created at the University of Colorado at
  Boulder.  The University of Colorado at Boulder makes no warranty
  about the suitability of this software for any purpose.  It is
  presented on an AS IS basis.]

******************************************************************************/

#include "util.h"
#include "array.h"
#include "st.h"
#include "cuddInt.h"
#include "cuddBdd.h"

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
static char rcsid[] DD_UNUSED = "$Id: cuddPwPt.c,v 1.3 1997/01/18 19:43:19 fabio Exp $";
#endif

/*---------------------------------------------------------------------------*/
/* Macro declarations                                                        */
/*---------------------------------------------------------------------------*/

/**AutomaticStart*************************************************************/

/*---------------------------------------------------------------------------*/
/* Static function prototypes                                                */
/*---------------------------------------------------------------------------*/

/**AutomaticEnd***************************************************************/


/*---------------------------------------------------------------------------*/
/* Definition of exported functions                                          */
/*---------------------------------------------------------------------------*/


/**Function********************************************************************

  Synopsis    [Returns a pointer to the one constant.]

  Description [Returns a pointer to the one constant. Used by the power
  package in SIS. For new code, use Cudd_ReadOne instead.]

  SideEffects [None]

  SeeAlso     [Cudd_ReadOne]

******************************************************************************/
bdd_node *
cmu_bdd_one(dd)
bdd_manager *dd;
{
    return((bdd_node *)((DdManager *)dd)->one);

} /* end of cmu_bdd_one */


/**Function********************************************************************

  Synopsis    [Returns a pointer to the zero constant.]

  Description [Returns a pointer to the zero constant. Used by the power
  package in SIS. For new code, use Cudd_ReadZero instead.]

  SideEffects [None]

  SeeAlso     [Cudd_ReadZero]

******************************************************************************/
bdd_node *
cmu_bdd_zero(dd)
bdd_manager *dd;
{
    return((bdd_node *)Cudd_Not(((DdManager *)dd)->one));

} /* end of cmu_bdd_zero */


/**Function********************************************************************

  Synopsis    [Returns the index of the top variable in a BDD.]

  Description [Returns the index of the top variable in a BDD. Used by
  the power package in SIS. For new code, use Cudd_ReadIndex instead.]

  SideEffects [None]

  SeeAlso     [Cudd_ReadIndex]

******************************************************************************/
int
cmu_bdd_if_index(dd, node)
bdd_manager *dd;
bdd_node *node;
{
    return(Cudd_Regular(node)->index);

} /* end of cmu_bdd_if_index */


/*---------------------------------------------------------------------------*/
/* Definition of internal functions                                          */
/*---------------------------------------------------------------------------*/

/*---------------------------------------------------------------------------*/
/* Definition of static functions                                            */
/*---------------------------------------------------------------------------*/
