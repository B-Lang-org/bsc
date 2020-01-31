GHC6	?= ghc
GHCFLAGS = -Wall -fno-warn-missing-signatures -fno-warn-name-shadowing -fno-warn-unused-matches -ffi -H128m -O2 -fasm

CC	= gcc 
CCFLAGS	= -g -c -Wall
USERCCFLAGS = 

CUDDDIR  = ../..

IPATH   = -I$(CUDDDIR)/include/
LPATH 	= -L$(CUDDDIR)/lib/cudd
CUDDLIBS = -lhcudd -lcudd -lcudd_mtr -lcudd_st -lcudd_epd -lcudd_util

AR	= ar -r 
LN	= ln -sf
RM	= rm -rf

.SUFFIXES: .o .c

HSOURCE = Main.hs CuddBdd.hs 
CSOURCE = cudd_interface.c
OFILES  = cudd_interface.o


all:	libhcudd.a

libhcudd.a:	cudd_interface.o
	$(AR) libhcudd.a cudd_interface.o
	./makelink.sh

cudd_interface.o:	cudd_interface.c cudd_interface.h
	$(CC) $(CCFLAGS) $(USERCCFLAGS) $(IPATH) -o cudd_interface.o cudd_interface.c


#.c.o:	$(CSOURCE) $(CHEADERS)
#	$(CC) -c $< $(CCFLAGS) 

test:	Makefile $(HSOURCE) $(CSOURCE) $(OFILES) libhcudd.a
	$(GHC6) $(GHCFLAGS) -o test --make Main.hs  $(CUDDLIBS) $(LPATH) $(IPATH)


run:	test
	./test 6

check:	test
	$(RM) test.out test.DIFF 
	./test 8 > test.out
	-diff test.out test.out.expected > test.DIFF
	cat test.DIFF

clean:
	$(RM) test *.o *.a *.hi
	$(RM) test.out test.DIFF 

full_clean: clean
	$(RM) $(CUDDDIR)/lib/CuddBdd.hs
	$(RM) $(CUDDDIR)/lib/CuddBdd.hi

