# $Id: Makefile,v 1.3 2001/03/19 07:34:37 fabio Exp fabio $
#
# obj: CUDD's C++ interface
#---------------------------------------------------------------------------
.SUFFIXES: .o .cc .u

#CXX	= g++
RANLIB	= ranlib
# Define EXE as .exe for MS-DOS and derivatives.
PURE	=
EXE	=
#EXE	= .exe

MFLAG	=
ICFLAGS = -g
XCFLAGS =
CXXFLAGS =
CFLAGS	= $(ICFLAGS) $(MFLAG) $(XCFLAGS) $(CXXFLAGS)
DDDEBUG =

LINTFLAGS = -u -n -DDD_STATS -DDD_CACHE_PROFILE -DDD_VERBOSE -DDD_DEBUG -DDD_UNIQUE_PROFILE

# this is to create the lint library
LINTSWITCH = -o

WHERE	= ..

INCLUDE = $(WHERE)/include

LIBS	= ./libobj.a $(WHERE)/cudd/libcudd.a $(WHERE)/mtr/libmtr.a \
	$(WHERE)/st/libst.a $(WHERE)/util/libutil.a $(WHERE)/epd/libepd.a

MNEMLIB =

BLIBS	= -kL. -klobj -kL$(WHERE)/cudd -klcudd -kL$(WHERE)/mtr -klmtr \
	-kL$(WHERE)/st -klst -kL$(WHERE)/util -klutil -kL$(WHERE)/epd -klepd

LINTLIBS = ./llib-lobj.ln $(WHERE)/cudd/llib-lcudd.ln \
	$(WHERE)/mtr/llib-lmtr.ln $(WHERE)/st/llib-lst.ln \
	$(WHERE)/util/llib-lutil.ln $(WHERE)/epd/llib-lepd.ln

LDFLAGS =

# files for the package
P	= obj
PSRC	= cuddObj.cc
PHDR	= cuddObj.hh $(INCLUDE)/cudd.h
POBJ	= $(PSRC:.cc=.o)
PUBJ	= $(PSRC:.cc=.u)
TARGET	= test$(P)$(EXE)
TARGETu = test$(P)-u

# files for the test program
SRC	= test$(P).cc
OBJ	= $(SRC:.cc=.o)
UBJ	= $(SRC:.cc=.u)

#------------------------------------------------------

lib$(P).a: $(POBJ)
	ar rv $@ $?
	$(RANLIB) $@

.cc.o: $(PHDR)
	$(CXX) -c $< -I$(INCLUDE) $(CFLAGS) $(DDDEBUG)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar rv $@ $?
	$(RANLIB) $@

.cc.u: $(PHDR)
	cxx -j $< -I$(INCLUDE) $(CFLAGS)

# if the header files change, recompile
$(POBJ): $(PHDR)
$(PUBJ): $(PHDR)
$(OBJ): $(PHDR)
$(UBJ): $(PHDR)

$(TARGET): $(SRC) $(OBJ) $(HDR) $(LIBS) $(MNEMLIB)
	$(PURE) $(CXX) $(CFLAGS) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm

# optimize (DECstations and Alphas only: uses u-code)
$(TARGETu): $(SRC) $(UBJ) $(HDR) $(LIBS:.a=.b)
	cxx -O3 -Olimit 1000 $(XCFLAGS) $(LDFLAGS) -o $@ $(UBJ) $(BLIBS) -lm

lint: llib-l$(P).ln

llib-l$(P).ln: $(PSRC) $(PHDR)
	lint $(LINTFLAGS) $(LINTSWITCH)$(P) -I$(INCLUDE) $(PSRC)

lintpgm: lint
	lint $(LINTFLAGS) -I$(INCLUDE) $(SRC) $(LINTLIBS)

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b llib-l$(P).ln tags

programs: $(TARGET) $(TARGETu) lintpgm

clean:
	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
	.pure core *.warnings

distclean: clean
	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
	*.bak *~ tags .gdb_history *.qv *.qx
