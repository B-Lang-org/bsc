# $Id$
#
#	Makefile for the Mnemosyne memory allocation tracker.
#
#	Marcus J. Ranum, 1990
#
#Options:
# define MALLOC_IS_VOIDSTAR if your system's malloc is declared as a (void *)
# otherwise, it is assumed to be a (char *). a "mall_t" is typedeffed in
# mnemconf.h and mnemosyne.h to implement this.
OPTNS	=	-DMALLOC_IS_VOIDSTAR
#OPTNS	=

#CC	= cc
RANLIB	= ranlib

#compiler flags
CFLAGS	=	-g $(OPTNS) $(XCFLAGS)

#loader flags
LDFLGS	=

HDRS	=	mnemosyne.h mnemconf.h

all: mnemalyse libmnem.a

mnemalyse: mnemalyse.o
	$(CC) $(LDFLGS) -o $@ mnemalyse.o

libmnem.a: mnemosyne.o
	ar rcv $@ mnemosyne.o
	$(RANLIB) $@

mtest: mtest.o libmnem.a
	$(CC) $(LDFLGS) -o $@ mtest.o libmnem.a

runmtest: all mtest
	@echo "running memory waster"
	mtest
	@echo "press return for symbol list"; read ff
	@cat mnem.syms
	@echo "press return for waste analysis"; read ff
	mnemalyse

clean:
	rm -f mtest core *.o mnem.dat mnem.syms

distclean: clean
	rm -f *.bak *~ libmnem.a mnemalyse 


mnemosyne.o: Makefile mnemosyne.c $(HDRS)
mnemalyse.o: Makefile mnemalyse.c $(HDRS)
