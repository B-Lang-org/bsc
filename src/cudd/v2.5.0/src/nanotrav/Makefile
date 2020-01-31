# $Id: Makefile,v 1.12 1999/08/31 19:10:05 fabio Exp fabio $
#
# nanotrav: simple FSM traversal program
#---------------------------------------------------------------------------
.SUFFIXES: .o .c .u

#CC	= gcc
#CC	= cc
RANLIB	= ranlib
#RANLIB	= :
PURE	=

EXE	=
#EXE	= .exe
TARGET	= nanotrav$(EXE)
TARGETu = nanotrav-u

WHERE	= ..

INCLUDE = $(WHERE)/include

LIBS	= $(WHERE)/dddmp/libdddmp.a $(WHERE)/cudd/libcudd.a \
	$(WHERE)/mtr/libmtr.a $(WHERE)/st/libst.a $(WHERE)/util/libutil.a \
	$(WHERE)/epd/libepd.a

MNEMLIB =
#MNEMLIB	= $(WHERE)/mnemosyne/libmnem.a

BLIBS	= -kL$(WHERE)/dddmp -kldddmp -kL$(WHERE)/cudd -klcudd -kL$(WHERE)/mtr \
	-klmtr -kL$(WHERE)/st -klst -kL$(WHERE)/util -klutil \
	-kL$(WHERE)/epd -klepd

LINTLIBS = $(WHERE)/llib-ldddmp.a $(WHERE)/cudd/llib-lcudd.ln \
	$(WHERE)/mtr/llib-lmtr.ln $(WHERE)/st/llib-lst.ln \
	$(WHERE)/util/llib-lutil.ln $(WHERE)/epd/llib-lepd.ln

SRC	= main.c bnet.c ntr.c ntrHeap.c ntrBddTest.c ntrMflow.c ntrZddTest.c \
	  ntrShort.c chkMterm.c ucbqsort.c
HDR	= bnet.h ntr.h $(WHERE)/include/dddmp.h $(WHERE)/include/cudd.h \
	$(WHERE)/include/cuddInt.h

OBJ	= $(SRC:.c=.o)
UBJ	= $(SRC:.c=.u)

MFLAG	=
#MFLAG	= -DMNEMOSYNE
ICFLAGS = -g -O6 -Wall
#ICFLAGS = -g -Wall
XCFLAGS = -DHAVE_IEEE_754 -DBSD
#XCFLAGS = -xtaso -ieee_with_no_inexact -tune host
CFLAGS	= $(ICFLAGS) $(MFLAG) $(XCFLAGS)
DDDEBUG =
#DDDEBUG = -DDD_STATS -DDD_VERBOSE -DDD_CACHE_PROFILE -DDD_UNIQUE_PROFILE -DDD_DEBUG

LDFLAGS =
#LDFLAGS = -jmpopt
#LDFLAGS = -non_shared -om -taso

LINTFLAGS = -u -n -DDD_STATS -DDD_CACHE_PROFILE -DDD_VERBOSE -DDD_DEBUG -DDD_UNIQUE_PROFILE

#------------------------------------------------------

$(TARGET): $(SRC) $(OBJ) $(HDR) $(LIBS) $(MNEMLIB)
	$(PURE) $(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm

.c.o: $(HDR)
	$(CC) -c $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)

# if the header files change, recompile
$(OBJ): $(HDR)
$(UBJ): $(HDR)

optimize_dec: $(TARGETu)

# optimize (DECstations only: uses u-code)
$(TARGETu): $(SRC) $(UBJ) $(HDR) $(LIBS:.a=.b)
	cc -O3 $(XCFLAGS) $(LDFLAGS) $(UBJ) -o $@ $(BLIBS) -lm

.c.u: $(SRC) $(HDR)
	cc -j -I$(INCLUDE) $(XCFLAGS) $<

lint: $(SRC) $(HDR) $(LINTLIBS)
	lint $(LINTFLAGS) -I$(INCLUDE) $(SRC) $(LINTLIBS)

tags: $(SRC) $(HDR)
	ctags $(SRC) $(HDR)

all: $(TARGET) $(TARGETu) lint tags

pixie: $(TARGETu)
	pixie $(TARGETu)

clean:
	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
	.pure core *.warnings

distclean: clean
	rm -f $(TARGET) $(TARGETu) *.bak *~ .gdb_history *.qv *.qx
