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

/* DO NOT INCLUDE "mnemosyne.h" !!! */
#include	<stdio.h>
#include	<ctype.h>
#include	<sys/types.h>
#include	<sys/file.h>

static	char	rcsid[] = "/fats/tools/hsv/mnemosyne/mnemalyse.c,v 1.1.1.1 1995/06/06 18:18:28 fabio Exp";

#include	"mnemconf.h"

extern	char	*index();

/*
post-processor to interpret memory allocation maps and search for
pointers that were allocated but never freed.

	Marcus J. Ranum, 1990. (mjr@decuac.dec.com)
*/


/*
simple and braindead, read in the ".lines" file, and store it in a
table by number. then read the pointer map, and crossref any unfreed
pointers. simple as dereferencing NULL...

this could use some cleaning and buffing, but it's damn effective as
it is. again, fancier symbol table routines would make this faster,
but who gives a damn? it only has to be faster than finding memory
leaks by hand...
*/

struct	xsym	{
	char	*dat;
	int	lnum;
	int	map;
	struct	xsym	*nxt;
};



main()
{
	register struct xsym	*sp;
	register struct xsym	*zp;
	struct	ptr	p;
	struct	xsym	*shash[HASHSIZ];
	char		inbuf[BUFSIZ];
	FILE		*lp;
	int		fd;

	/* statistics */
	int		ptrcnt = 0;
	int		ptrbad = 0;
	int		ptrlos = 0;

	/* to chop up lines */
	char		*cpmap;
	char		*cpcalls;
	char		*cpave;
	char		*cplnum;
	char		*cpfnam;

	for(fd = 0; fd < HASHSIZ; fd++)
		shash[fd] = (struct xsym *)0;

	if((lp = fopen(LINESFILE,"r")) == (FILE *)0) {
		perror(LINESFILE);
		exit(1);
	}

	if((fd = open(PTRFILE,O_RDONLY|O_RDWR)) < 0) {
		perror(PTRFILE);
		exit(1);
	}

	/* this is ugly, but I refuse to trust !@(#&U!@#&! sscanf() */
	while((cpmap = fgets(inbuf,sizeof(inbuf),lp)) != (char *)0) {
		if(inbuf[0] == '#')
			continue;

		sp = (struct xsym *)malloc(sizeof(struct xsym));
		if(sp == (struct xsym *)0) {
			perror("malloc");
			exit(1);
		}
		sp->lnum = sp->map = 0;

		if((cpcalls = index(cpmap,'\t')) != (char *)0)
			*cpcalls++ = '\0';

		if((cpave = index(cpcalls,'\t')) != (char *)0)
			*cpave++ = '\0';

		if((cplnum = index(cpave,'\t')) != (char *)0)
			*cplnum++ = '\0';

		if((cpfnam = index(cplnum,'\t')) != (char *)0)
			*cpfnam++ = '\0';

		/* setup symbol */
		sp->map = atoi(cpmap);

		if(cplnum == (char *)0)
			sp->lnum = -1;
		else
			sp->lnum = atoi(cplnum);

		if(cpfnam != (char *)0) {
			char	*x;
			if((x = index(cpfnam,'\n')) != (char *)0)
				*x = '\0';

			sp->dat = malloc((unsigned)(strlen(cpfnam) + 1));
			if(sp->dat == (char *)0) {
				perror("malloc");
				exit(1);
			}
			(void)strcpy(sp->dat,cpfnam);
		} else
			sp->dat = "unknown";

		/* check to make sure it is not already in table */
		zp = shash[sp->map % HASHSIZ];
		while(zp != (struct xsym *)0) {
			if(zp->map == sp->map) {
				(void)fprintf(stderr,
				"mnemalyse: duplicate map entry ignored");
				(void)fprintf(stderr,
				" (point at both %s and %s)\n",sp->dat,zp->dat);
				(void)free(sp);

				/* can't free dat - may not be malloced! */
				sp = (struct xsym *)0;
				break;
			}
			zp = zp->nxt;
		}

		/* shrug, link it in */
		if(sp != (struct xsym *)0) {
			sp->nxt = shash[sp->map % HASHSIZ];
			shash[sp->map % HASHSIZ] = sp;
		}
	}
	(void)fclose(lp);

	while(read(fd,(char *)&(p.dsk),sizeof(p.dsk)) == sizeof(p.dsk)) {

		/* if the pointer was not deallocated, note it */
		if(p.dsk.siz != 0) {
			zp = shash[p.dsk.smap % HASHSIZ];
			while(zp != (struct xsym *)0) {
				if(zp->map == p.dsk.smap) {
					printf("%d bytes missing %s line:%d\n",
					p.dsk.siz,zp->dat,zp->lnum);
				}
				zp = zp->nxt;
			}
			ptrbad++;
			ptrlos += p.dsk.siz;
		}
		ptrcnt++;
	}

	printf("%d pointers, %d lost totalling %d bytes\n",
		ptrcnt,ptrbad,ptrlos);
	exit(0);
}
