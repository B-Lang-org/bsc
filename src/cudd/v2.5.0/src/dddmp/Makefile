#----------------------------------------------------------------------------#
# Makefile for the dddmp distribution kit                                    #
# dddmp: Decision Diagram DuMP                                               #
#        (storage and retrieval of BDDs, ADDs and CNF formulas)              #
# Revision: Version 2.0.2, February 01, 2004                                 #
#----------------------------------------------------------------------------#

# Commands Available:
# make
#    it makes the library libdddmp.a
# make testdddmp
#    it makes the testdddmp program, which allows to test the dddmp
#    package
# make clean
#    it cleans dddmp
# make distclean
#    it cleans dddmp (as clean) with libraries and executable
#    files

#----------------------------------------------------------------------------#
# Configuration Section                                                      #
# uncomment the desired options/sections                                     #
#----------------------------------------------------------------------------#

#--------------------#
# Define Directories #
#--------------------#

# Cudd directory
WHERE	= ..
#WHERE	= ../cudd-2.4.0

# Include directory (Cudd include files)
INCLUDE = $(WHERE)/include

#------------------------#
# Define C Compiler Used #
#------------------------#

#CC	= gcc
#CC	= g++
#CC	= cc
#CC	= icc
#CC	= ecc
#CC	= /usr/ucb/cc
#CC	= c89

.SUFFIXES: .o .c .u

#---------------#
# Define ranlib #
#---------------#

# For machines with ranlib and you think it is needed
RANLIB	= ranlib
# For machines which either do not have ranlib or can do without it
#RANLIB	= :

#----------------------------------#
# Define Machine Independent Flags #
#----------------------------------#

# Settings for cc
#ICFLAGS        =
#ICFLAGS	= -g
#ICFLAGS        = -O
# Settings for optimized code with gcc
#ICFLAGS	= -g -Wall
#ICFLAGS	= -g -O3 -Wall
ICFLAGS	= -g -O6 -Wall
      
#--------------------------------#
# Define Machine Dependent Flags #
#--------------------------------#

# When no special flags are needed
#XCFLAGS	= -DHAVE_IEEE_754 -DBSD
# Linux with Gcc 2.8.1 or higher on i686.
#XCFLAGS	= -mcpu=pentiumpro -malign-double -DHAVE_IEEE_754 -DBSD
# Gcc 3.3.2 or higher on i686.
XCFLAGS	= -mcpu=pentium4 -malign-double -DHAVE_IEEE_754 -DBSD
# For Solaris, BSD should not be replaced by UNIX100.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -DEPD_BIG_ENDIAN
# New native compiler for the Alphas; 64-bit pointers. 
#XCFLAGS	= -g3 -O4 -std -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
# New native compiler for the Alphas; 32-bit pointers.
#XCFLAGS	= -g3 -O4 -std -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -xtaso -DSIZEOF_LONG=8
#  Windows95/98/NT/XP with Cygwin tools
#XCFLAGS	= -mcpu=pentiumpro -malign-double -DHAVE_IEEE_754 -DHAVE_GETRLIMIT=0 -DRLIMIT_DATA_DEFAULT=67108864

#---------------------------------------------#
# Define Level of Self-Checking and Verbosity #
#---------------------------------------------#

# ... for the CUDD package
#DDDEBUG = -DDD_DEBUG -DDD_VERBOSE -DDD_STATS -DDD_CACHE_PROFILE -DDD_UNIQUE_PROFILE -DDD_COUNT
DDDEBUG	=

# ... for the MTR package
#MTRDEBUG = -DMTR_DEBUG
MTRDEBUG =

# ... for the DDDMP package
#DDDMPDEBUG = -DDDDMP_DEBUG
DDDMPDEBUG =

#-----------------------#
# Define Loader Options #
#-----------------------#

LDFLAGS	=
# This may produce faster code on the DECstations.
#LDFLAGS	= -jmpopt -Olimit 1000
# This may be necessary under some old versions of Linux.
#LDFLAGS	= -static
# This normally makes the program faster on the DEC Alphas.
#LDFLAGS	= -non_shared -om
# This is for 32-bit pointers on the DEC Alphas.
#LDFLAGS	= -non_shared -om -taso
#LDFLAGS	= -non_shared -taso

#-------------#
# Define PURE #
#-------------#

PURE =
# ... as purify to link with purify.
#PURE	= purify
# ... as quantify to link with quantify.
#PURE	= quantify

#------------#
# Define EXE #
#------------#

EXE	=
# ... as .exe for MS-DOS and derivatives.
#EXE	= .exe

#----------------------------------------------------------------------------#
# Files for the Package                                                      #
#----------------------------------------------------------------------------#

P	= dddmp
PSRC    = dddmpStoreBdd.c dddmpStoreAdd.c dddmpStoreCnf.c \
	  dddmpLoad.c dddmpLoadCnf.c \
	  dddmpNodeBdd.c dddmpNodeAdd.c dddmpNodeCnf.c \
	  dddmpStoreMisc.c dddmpUtil.c dddmpBinary.c dddmpConvert.c \
          dddmpDbg.c 
PHDR    = dddmp.h dddmpInt.h $(INCLUDE)/cudd.h $(INCLUDE)/cuddInt.h
POBJ	= $(PSRC:.c=.o)
PUBJ	= $(PSRC:.c=.u)
TARGET	= test$(P)$(EXE)
TARGETu = test$(P)-u

# files for the test program
SRC	= test$(P).c
OBJ	= $(SRC:.c=.o)
UBJ	= $(SRC:.c=.u)

#----------------------------------------------------------------------------#
# Rules to compile and build libraries and executables                       #
#----------------------------------------------------------------------------#

#MFLAG =
MFLAG   = -DMNEMOSYNE
MNEMLIB	= ../mnemosyne/libmnem.a

# This is to create the lint library
LINTFLAGS = -u -n
LINTSWITCH = -o

LIBS	= ./libdddmp.a $(WHERE)/cudd/libcudd.a $(WHERE)/mtr/libmtr.a \
	$(WHERE)/st/libst.a $(WHERE)/util/libutil.a $(WHERE)/epd/libepd.a

MNEMLIB =

BLIBS	= -kL. -kldddmp -kL$(WHERE)/cudd -klcudd -kL$(WHERE)/mtr -klmtr \
	-kL$(WHERE)/st -klst -kL$(WHERE)/util -klutil

LINTLIBS = ./llib-ldddmp.ln $(WHERE)/cudd/llib-lcudd.ln \
	$(WHERE)/mtr/llib-lmtr.ln $(WHERE)/st/llib-lst.ln \
	$(WHERE)/util/llib-lutil.ln

lib$(P).a: $(POBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.o: $(PHDR)
	$(CC) -c $< -I$(INCLUDE) $(ICFLAGS) $(XCFLAGS) $(DDDEBUG) $(MTRDEBUG) $(DDDMPDEBUG) $(LDFLAGS)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.u: $(PHDR)
	cc -c $< -I$(INCLUDE) $(CFLAGS)

# if the header files change, recompile
$(POBJ): $(PHDR)
$(PUBJ): $(PHDR)
$(OBJ): $(PHDR)
$(UBJ): $(PHDR)

$(TARGET): $(SRC) $(OBJ) $(PHDR) $(LIBS) $(MNEMLIB)
	$(PURE) $(CC) $(ICFLAGS) $(XCFLAGS) $(DDDEBUG) $(MTRDEBUG) $(DDDMPDEBUG) $(LDFLAGS) -o $@ $(OBJ) $(LIBS) $(MNEMLIB) -lm

# optimize (DECstations and Alphas only: uses u-code)
$(TARGETu): $(SRC) $(UBJ) $(PHDR) $(LIBS:.a=.b)
	cc -O3 -Olimit 1000 $(XCFLAGS) $(LDFLAGS) -o $@ $(UBJ) $(BLIBS) -lm

lint: llib-l$(P).ln

llib-l$(P).ln: $(PSRC) $(PHDR)
	lint $(LINTFLAGS) $(LINTSWITCH)$(P) -I$(INCLUDE) $(PSRC)

lintpgm: lint
	lint $(LINTFLAGS) -I$(INCLUDE) $(SRC) $(LINTLIBS)

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b llib-l$(P).ln tags

programs: $(TARGET) $(TARGETu) lintpgm

#----------------------------------------------------------------------------#
# Clean the Package                                                          #
#----------------------------------------------------------------------------#

clean:
	rm -f *.o *.u mon.out gmon.out *.pixie *.Addrs *.Counts mnem.* \
	.pure core *.warnings

distclean: clean
	rm -f $(TARGET) $(TARGETu) lib*.a lib$(P).b llib-l$(P).ln \
	*.bak *~ tags .gdb_history *.qv *.qx




