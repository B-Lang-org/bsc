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
#include	<sys/types.h>
#include	<sys/file.h>

/* shared stuff - and decl of struct ptr */
#include	"mnemconf.h"

static	char	rcsid[] = "/fats/tools/hsv/mnemosyne/mnemosyne.c,v 1.1.1.1 1995/06/06 18:18:28 fabio Exp";


/*
malloc() realloc() and family wrappers - these functions manage a set
of data files that are updated whenever a pointer is allocated or freed,
as well as gathering stats about dynamic memory use and leakage.

	Marcus J. Ranum, 1990. (mjr@decuac.dec.com)
*/


/*
there is some egregious use of globals, void functions, and whatnot
in this code. it is mostly due to the constraint that nothing must
be visible to the outside, and that the code must be structurally
simple. error checking is pitched out the window in spots, since an
error in the mnemosyne code should not affect whatever is being
instrumented if at all possible. this means no errors, no signals,
nothing. (this message brought to you by my ego, in case you think
I don't know how to write better code than this) :)

mjr, hacking on Christmas, 1990.
*/

#define	REC_UNINIT	000
#define	REC_INITTED	001
#define	REC_ERR		002
#define	REC_ON		010
#define	REC_ONOFF	020
static	int	rec_state = REC_UNINIT;

/*
this method of storing the symbol maps is not the most efficient, but
then that's not important here, since all we're trying to do is find
memory leaks. if you choose to improve the symbol management to use
bucketed hash tables, please contact the author and the code will be
updated :) - besides, since we do file I/O every time you malloc or
free something, there's no way in hell this is going to set any new
records for speed.
*/


/* storage for code/line # entry */
struct	sym	{
	char		*labl;
	int		lineno;
	int		mapno;
	int		mallcnt;
	float		avsiz;
	struct	sym	*next;
};



/* static symbol map */
static	struct	{
	FILE	*fp;
	FILE	*log;
	int	fd;

	long	nalloc;		/* count of allocations */
	long	nrlloc;		/* count of re-allocations */
	long	nfree;		/* count of frees */
	long	nbfree;		/* count of bad frees */
	long	ninuse;		/* known allocated memory in use */
	float	avgsiz;		/* average malloc size */

	/* one entry per pointer returned by malloc */
	int	pmap;		/* current next ptr map to alloc */
	struct	ptr	*phash[HASHSIZ];

	/* one entry per line of code that calls malloc/realloc, etc */
	int	lmap;		/* current next line map to alloc */
	struct	sym	*shash[HASHSIZ];	/* hash access */
} map;




/* print a locale record with checks for closed log file */
static	void
ploc(lab,lin,siz)
char	*lab;
int	lin;
int	siz;
{
	if(map.log == (FILE *)0)
		return;
	if(lab != (char *)0)
		(void)fprintf(map.log," \"%s\"",lab);
	else
		(void)fprintf(map.log," unknown");
	if(lin != -1)
		(void)fprintf(map.log," line:%d",lin);
	if(siz != -1)
		(void)fprintf(map.log," size:%d",siz);
}




/* print a symbol map entry with checks for closed log file */
static	void
psym(s)
struct	sym	*s;
{
	if(map.log == (FILE *)0)
		return;
	(void)fprintf(map.log," \"%s\"",s->labl);
	if(s->lineno != -1)
		(void)fprintf(map.log," line:%d",s->lineno);
}




/* output a warning message with checks for closed log file */
static	void
pmsg(s)
char	*s;
{
	if(map.log == (FILE *)0)
		return;
	(void)fprintf(map.log,"%s",s);
}




/* save an entry to the .lines file */
static	void
savesym(s)
struct	sym	*s;
{
	if(map.fp == (FILE *)0)
		return;

	(void)fprintf(map.fp,"%d\t%d\t%.1f\t%d\t%s\n",
		s->mapno,s->mallcnt,s->avsiz,s->lineno,s->labl);
}




/* save an entry in the pointer map file */
static	void
saveptr(p)
register struct	ptr	*p;
{
	if(lseek(map.fd,(off_t)(p->map * sizeof(p->dsk)),0) !=
		(off_t)(p->map * sizeof(p->dsk))) {
		pmsg("mnemosyne: cannot seek in pointer map file\n");
		rec_state |= REC_ERR;
		return;
	}

	if(write(map.fd,(char *)&(p->dsk),sizeof(p->dsk)) != sizeof(p->dsk)) {
		pmsg("mnemosyne: cannot write in pointer map file\n");
		rec_state |= REC_ERR;
		return;
	}
}




/* initialize everything - symbol tables, files, and maps */
static	void
initmap()
{
	register int	xp;

	if(rec_state & REC_INITTED)
		return;

	if((map.fp = fopen(LINESFILE,"w")) == (FILE *)0)
		return;
	if((map.fd = open(PTRFILE,O_RDWR|O_CREAT|O_TRUNC,0600)) < 0) {
		(void)fclose(map.fp);
		return;
	}

	map.log = stderr;
	map.lmap = map.pmap = 0;
	map.nalloc = map.nrlloc = map.nfree = map.nbfree = 0L;
	map.ninuse = 0L;
	map.avgsiz = 0.0;

	for(xp = 0; xp < HASHSIZ; xp++) {
		map.phash[xp] = (struct ptr *)0;
		map.shash[xp] = (struct sym *)0;
	}

	rec_state = REC_INITTED | REC_ON;
}




/* set logging to a FILE * */
void
mnem_setlog(fp)
FILE	*fp;
{
	map.log = fp;
}




/* return state of the recorder */
int
mnem_recording()
{
	return((rec_state & REC_ON) && !(rec_state & REC_ERR));
}




/* turn on or off recording */
int
mnem_setrecording(val)
int	val;
{
	if(!(rec_state & REC_INITTED))
		initmap();

	if(val)
		rec_state |= REC_ON;
	else
		rec_state &= ~REC_ON;

	if(map.fp != (FILE *)0)
		(void)fflush(map.fp);

	rec_state |= REC_ONOFF;
	return(0);
}




/* lookup a pointer record - search pointer hash table */
static struct	ptr	*
lookupptr(ptr)
mall_t	ptr;
{
	register struct	ptr	*p;

	/* this probably give simply terrible hash performance */
	p = map.phash[(unsigned long)ptr % HASHSIZ];
	while(p != (struct ptr *)0) {
		if(ptr == p->ptr)
			return(p);
		p = p->next;
	}
	return((struct ptr *)0);
}




/*
 * polynomial conversion ignoring overflows
 * [this seems to work remarkably well, in fact better
 * then the ndbm hash function. Replace at your own risk]
 * use: 65599	nice.
 *      65587   even better. 
 * author: oz@nexus.yorku.ca
 */
static unsigned int
dbm_hash(str)
register char *str;
{
	register unsigned int n = 0;

	while(*str != '\0')
		n = *str++ + 65599 * n;
	return(n);
}




/* lookup a line/source entry by name (search hash table) */
static struct	sym	*
lookupsymbyname(nam,lin)
char	*nam;
int	lin;
{
	register struct sym	*s;
	char			*p = nam;

	if(p == (char *)0)
		p = "unknown";

	s = map.shash[(dbm_hash(p) + lin) % HASHSIZ];
	while(s != (struct sym *)0) {
		if(!strcmp(s->labl,nam) && s->lineno == lin)
			return(s);
		s = s->next;
	}

	return((struct sym *)0);
}




/* lookup a line/source entry by number (exhaustively search hash table) */
static struct	sym	*
lookupsymbynum(num)
int	num;
{
	register struct sym	*s;
	register int		x;

	for(x = 0; x < HASHSIZ; x++) {
		s = map.shash[x];
		while(s != (struct sym *)0) {
			if(s->mapno == num)
				return(s);
			s = s->next;
		}
	}
	return((struct sym *)0);
}



/* stuff a pointer's value in the pointer map table */
static	void
storeptr(ptr,siz,lab,lin)
mall_t	ptr;
int	siz;
char	*lab;
int	lin;
{
	register struct	ptr	*p;
	register struct	sym	*s;
	int			hv;

	/*
	is there is no existing symbol entry for this line of code...
	we must needs make one - and painful it is...
	*/
	if((s = lookupsymbyname(lab,lin)) == (struct sym *)0) {
		s = (struct sym *)malloc(sizeof(struct sym));
		if(s == (struct sym *)0) {
			pmsg("mnemosyne: cannot allocate sym entry\n");
			rec_state |= REC_ERR;
			return;
		}

		/*
		this is funky - since we know the label is (?)
		compiled-in, we can just keep a pointer to it,
		rather than copying our own version of it.
		*/
		if(lab != (char *)0)
			s->labl = lab;
		else
			s->labl = "unknown";

		s->mapno = map.lmap++;

		/* add sym to hash table */
		s->next = map.shash[hv = ((dbm_hash(s->labl) + lin) % HASHSIZ)];
		map.shash[hv] = s;
 
		s->lineno = lin;
		s->mallcnt = 1;
		s->avsiz = siz;
		savesym(s);
	} else {
		/* found an already defined symbol. store some averages */
		s->avsiz = ((s->avsiz * s->mallcnt) + siz) / (s->mallcnt + 1);
		(s->mallcnt)++;
	}

	p = lookupptr(ptr);
	if(p != (struct ptr *)0 && p->dsk.siz != 0) {
		struct	sym	*x;

		pmsg("pointer re-allocated without being freed");
		ploc(lab,lin,(int)siz);
		if((x = lookupsymbynum(p->dsk.smap)) != (struct sym *)0) {
			pmsg(" last allocated ");
			psym(x);
		}
		pmsg("\n");
	}

	/* heavy sigh. no entry for this pointer. make one. */
	if(p == (struct ptr *)0) {
		p = (struct ptr *)malloc(sizeof(struct ptr));
		if(p == (struct ptr *)0) {
			pmsg("mnemosyne: cannot expand pointer table\n");
			rec_state |= REC_ERR;
			return;
		}

		/* link it in */
		p->next = map.phash[(unsigned long)ptr % HASHSIZ];
		map.phash[(unsigned long)ptr % HASHSIZ] = p;
	}

	/* if we get to here (hazoo! hazaa!) both 's' and 'p' are OK */
	p->ptr = ptr;
	p->dsk.siz = siz;
	p->dsk.smap = s->mapno;
	p->map = map.pmap++;

	/* store the size */
	map.ninuse += siz;

	saveptr(p);
}




/*
mark a pointer as now being free. note that a 1 is returned IF 
the actual value should NOT be really passed to free()
*/
static	int
freeptr(ptr,lab,lin)
mall_t	ptr;
char	*lab;
int	lin;
{
	register struct	ptr	*p;

	p = lookupptr(ptr);
	if(p == (struct ptr *)0) {
		pmsg("pointer freed that was never allocated");
		ploc(lab,lin,-1);
		pmsg("\n");
		return(1);
	}

	if(p != (struct ptr *)0 && p->dsk.siz == 0) {
		struct	sym	*x;

		pmsg("pointer re-freed when already free");
		ploc(lab,lin,-1);
		if((x = lookupsymbynum(p->dsk.smap)) != (struct sym *)0) {
			pmsg(" last allocated:");
			psym(x);
		}
		pmsg("\n");
		return(1);
	}

	/* get some free */
	map.ninuse -= p->dsk.siz;

	/* write in the map that it is free */
	p->dsk.siz = 0;
	saveptr(p);

	return(0);
}




/* pretend we are malloc() */
mall_t
mnem_malloc(siz,lab,lin)
unsigned	siz;
char		*lab;
int		lin;
{
	mall_t ret;

	if(!(rec_state & REC_INITTED))
		initmap();

	if((ret = malloc(siz)) == (mall_t)0) {
		pmsg("malloc returned null pointer at");
		ploc(lab,lin,(int)siz);
		pmsg("\n");
		return(ret);
	}

	if((rec_state & REC_ON) && !(rec_state & REC_ERR))
		storeptr(ret,(int)siz,lab,lin);

	map.avgsiz = ((map.avgsiz * map.nalloc) + siz) / (map.nalloc + 1);
	map.nalloc++;
	return(ret);
}




/* pretend we are calloc() */
mall_t
mnem_calloc(cnt,siz,lab,lin)
unsigned	cnt;
unsigned	siz;
char		*lab;
int		lin;
{
	mall_t ret;

	if(!(rec_state & REC_INITTED))
		initmap();

	if((ret = calloc(cnt,siz)) == (mall_t)0) {
		pmsg("calloc returned null pointer at");
		ploc(lab,lin,(int)(siz * cnt));
		pmsg("\n");
		return(ret);
	}

	if((rec_state & REC_ON) && !(rec_state & REC_ERR))
		storeptr(ret,(int)(cnt * siz),lab,lin);

	map.avgsiz = ((map.avgsiz * map.nalloc) + siz) / (map.nalloc + 1);
	map.nalloc++;
	return(ret);
}




/* pretend we are realloc() */
mall_t
mnem_realloc(ptr,siz,lab,lin)
mall_t		ptr;
unsigned	siz;
char		*lab;
int		lin;
{
	mall_t ret;

	if(!(rec_state & REC_INITTED))
		initmap();

	if((ret = realloc(ptr,siz)) == (mall_t)0) {
		pmsg("realloc returned null pointer at");
		ploc(lab,lin,(int)siz);
		pmsg("\n");
		return(ret);
	}

	if((rec_state & REC_ON) && !(rec_state & REC_ERR)) {
		if(!freeptr(ptr,lab,lin))
			storeptr(ret,(int)siz,lab,lin);
	}

	map.nrlloc++;
	return(ret);
}





/* pretend we are free() */
void
mnem_free(ptr,lab,lin)
mall_t		ptr;
char		*lab;
int		lin;
{
	if(!(rec_state & REC_INITTED))
		initmap();

	if((rec_state & REC_ON) && !(rec_state & REC_ERR))
		if(freeptr(ptr,lab,lin) == 0) {
			(void)free(ptr);
			map.nfree++;
		} else
			map.nbfree++;
}




/* dump everything we know about nothing in particular */
int
mnem_writestats()
{
	register struct sym	*s;
	register int		x;

	if(map.fp == (FILE *)0)
		return(-1);

	(void)fseek(map.fp,0L,0);

	/* dump our life's story */
	(void)fprintf(map.fp,"#total allocations:%ld\n",map.nalloc);
	(void)fprintf(map.fp,"#total re-allocations:%ld\n",map.nrlloc);
	(void)fprintf(map.fp,"#total frees:%ld\n",map.nfree);

	if(map.nbfree != 0L)
		(void)fprintf(map.fp,"#bad/dup frees:%ld\n",map.nbfree);

	(void)fprintf(map.fp,"#total allocated never freed:%ld\n",map.ninuse);

	(void)fprintf(map.fp,"#average size of allocations:%.1f\n",map.avgsiz);

	/* note if we detected an internal error */
	if(rec_state & REC_ERR)
		(void)fprintf(map.fp,
			"#(figures likely inaccurate due to error)\n");

	/* note if the system was on all the time ? */
	if(!(rec_state & REC_ON) || (rec_state & REC_ONOFF))
		(void)fprintf(map.fp,
			"#(figures likely inaccurate as recording was off)\n");

	/* write the legend */
	(void)fprintf(map.fp,"#map#\tcalls\tave\tline#\tfile\n");

	for(x = 0; x < HASHSIZ; x++) {
		s = map.shash[x];
		while(s != (struct sym *)0) {
			savesym(s);
			s = s->next;
		}
	}

	(void)fflush(map.fp);
	return(0);
}
