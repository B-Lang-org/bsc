/*
 * memcmp.c --
 *
 *	Source code for the "memcmp" library routine.
 *
 * Copyright (c) 1998 Sun Microsystems, Inc.
 *
 * See the file "license.terms" for information on usage and redistribution of
 * this file, and for a DISCLAIMER OF ALL WARRANTIES.
 *
 * RCS: @(#) $Id: memcmp.c,v 1.4 2007/01/22 09:15:50 dkf Exp $
 */

#include "tclPort.h"

/*
 * Here is the prototype just in case it is not included in tclPort.h.
 */

int		memcmp(CONST VOID *s1, CONST VOID *s2, size_t n);

/*
 *----------------------------------------------------------------------
 *
 * memcmp --
 *
 *	Compares two bytes sequences.
 *
 * Results:
 *	Compares its arguments, looking at the first n bytes (each interpreted
 *	as an unsigned char), and returns an integer less than, equal to, or
 *	greater than 0, according as s1 is less than, equal to, or greater
 *	than s2 when taken to be unsigned 8 bit numbers.
 *
 * Side effects:
 *	None.
 *
 *----------------------------------------------------------------------
 */

int
memcmp(
    CONST VOID *s1,		/* First string. */
    CONST VOID *s2,		/* Second string. */
    size_t n)			/* Length to compare. */
{
    CONST unsigned char *ptr1 = (CONST unsigned char *) s1;
    CONST unsigned char *ptr2 = (CONST unsigned char *) s2;

    for ( ; n-- ; ptr1++, ptr2++) {
	unsigned char u1 = *ptr1, u2 = *ptr2;

	if (u1 != u2) {
	    return (u1-u2);
	}
    }
    return 0;
}

/*
 * Local Variables:
 * mode: c
 * c-basic-offset: 4
 * fill-column: 78
 * End:
 */
