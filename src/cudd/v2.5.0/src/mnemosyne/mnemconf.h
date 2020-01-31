/************************************************************************
 *									*
 *			Copyright (c) 1985 by				*
 *		Digital Equipment Corporation, Maynard, MA		*
 *			All rights reserved.				*
 *									*
 *   The information in this software is subject to change  without	*
 *   notice  and should not be construed as a commitment by Digital	*
 *   Equipment Corporation.						*
 *									*
 *   Digital assumes no responsibility for the use  or  reliability	*
 *   of its software on equipment which is not supplied by Digital.	*
 *									*
 *   Redistribution and use in source and binary forms are permitted	*
 *   provided that the above copyright notice and this paragraph are	*
 *   duplicated in all such forms and that any documentation,		*
 *   advertising materials, and other materials related to such		*
 *   distribution and use acknowledge that the software was developed	*
 *   by Digital Equipment Corporation. The name of Digital Equipment	*
 *   Corporation may not be used to endorse or promote products derived	*
 *   from this software without specific prior written permission.	*
 *   THIS SOFTWARE IS PROVIDED ``AS IS'' AND WITHOUT ANY EXPRESS OR	*
 *   IMPLIED WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE IMPLIED	*
 *   WARRANTIES OF MERCHANTIBILITY AND FITNESS FOR A PARTICULAR PURPOSE.*
 *   Do not take internally. In case of accidental ingestion, contact	*
 *   your physician immediately.					*
 *									*
 ************************************************************************/

#ifndef	_INCL_MNEMCONF_H

/*
/fats/tools/hsv/mnemosyne/mnemconf.h,v 1.1.1.1 1995/06/06 18:18:29 fabio Exp
*/

/*
site specific and shared internal data structures used by mnemosyne.
the only data structure that may need to be shared is the struct ptr,
which is defined herein.

	Marcus J. Ranum, 1990. (mjr@decuac.dec.com)
*/



/* if your machine has malloc and all declared as a (void *) not a (char *) */
#ifdef	MALLOC_IS_VOIDSTAR
typedef	void	*mall_t;
#else
typedef	char	*mall_t;
#endif


/* size of internal hash tables - don't go wild - this is slow anyhow */
#define	HASHSIZ		2027


/* names of files to write */
#define	LINESFILE	"mnem.syms"
#define	PTRFILE		"mnem.dat"


extern	mall_t	malloc();
extern	mall_t	realloc();
extern	mall_t	calloc();
extern	void	free();


/*
storage for a pointer map entry - the only data structure we share
a whole mess of these get written to mnem.dat as calls to malloc and
whatnot are made. the distinction between an *allocated* pointer and
and unallocated one is that 'siz' is 0 in freed ptrs. this is used
by the post-processor to look for memory leaks.
*/
struct	ptr	{
	mall_t		ptr;	/* pointer to allocated memory */
	int		map;	/* this pointer's map # */
	struct	ptr	*next;

	/* only part that gets written to the disk */
	struct	{
		unsigned	siz;	/* size allocated (or 0) */
		int		smap;	/* symbol map # */
	} dsk;
};

#define	_INCL_MNEMCONF_H
#endif
