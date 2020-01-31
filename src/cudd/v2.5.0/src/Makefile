# $Id$
#
# Makefile for the CUDD distribution kit
#---------------------------------------------------------------------------

# Get the platform information
TOP := ../../../..
include $(TOP)/platform.mk

# Beginning of the configuration section. These symbol definitions can
# be overridden from the command line.

# C++ compiler
#CXX	= g++
#CXX	= icpc
#CXX	= ecpc
#CXX	= CC
#CXX	= /usr/local/opt/SUNWspro/bin/CC
#CXX	= cxx

# Specific options for compilation of C++ files.
CXXFLAGS =
# Stricter standard conformance for g++.
#CXXFLAGS = -std=c++98
# For Sun CC version 5, this invokes compatibility mode.
#CXXFLAGS = -compat
# On some versions of UP-UX, it is necessary to pass the option +a1
# to CC for the C++ test program to compile successfully.
#CXXFLAGS = +a1

# C compiler used for all targets except optimize_dec, which always uses cc.
#CC	= cc
#CC	= /usr/local/opt/SUNWspro/bin/cc
#CC	= gcc
#CC	= icc
#CC	= ecc
#CC	= /usr/ucb/cc
#CC	= c89
#CC	= $(CXX)

# On some machines ranlib is either non-existent or redundant.
# Use the following definition if your machine has ranlib and you think
# it is needed.
RANLIB	= ranlib
# Use the following definition if your machine either does not have
# ranlib (e.g., SUN running solaris) or can do without it (e.g., DEC Alpha).
#RANLIB	= :

# Use ICFLAGS to specify machine-independent compilation flags.
# These three are typical settings for cc.
#ICFLAGS	= -g
#ICFLAGS	= -O
#ICFLAGS	=
# These two are typical settings for optimized code with gcc.
#ICFLAGS	= -g -O3 -Wall
ICFLAGS	= -g -O3

# Use XCFLAGS to specify machine-dependent compilation flags.
# For some platforms no special flags are needed.
#XCFLAGS	= -DHAVE_IEEE_754 -DBSD
#
ifeq ($(OSTYPE), Linux)
#==========================
#  Linux on x86
#
$(warning machine type is $(MACHTYPE)) 
ifeq ($(MACHTYPE),$(findstring $(MACHTYPE), i386 i486 i586 i686))
XCFLAGS	= -malign-double -DHAVE_IEEE_754 -DBSD
#
#==========================
#  Linux on x86_64
#
else # not x86
ifeq ($(MACHTYPE),$(findstring $(MACHTYPE), x86_64))
XCFLAGS	= -DHAVE_IEEE_754 -DBSD -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
#
#==========================
# Unrecognized Linux system
else # not x86_64
$(error MACHTYPE environment not recognized for Linux: $(MACHTYPE))
endif # if/else x86_64
endif # if/else x86
#==========================
else # not Linux
ifeq ($(OSTYPE), Darwin)
#==========================
#  Mac OS X on x86
#
ifeq ($(MACHTYPE),$(findstring $(MACHTYPE), i386))
XCFLAGS       = -DHAVE_IEEE_754 -fno-common
#==========================
#  Mac OS X on x86_64
#
else # not x86
ifeq ($(MACHTYPE),$(findstring $(MACHTYPE), x86_64))
XCFLAGS       = -DHAVE_IEEE_754 -fno-common -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
#==========================
# Unrecognized Mac OS X system
else # not i386
$(error MACHTYPE environment not recognized for Darwin: $(MACHTYPE))
endif # if/else x86_64
endif # if/else x86
#==========================
else # not Darwin
$(error OSTYPE environment not recognized: $(OSTYPE))
endif # if/else Darwin
endif # if/else Linux

# Other possibilities
#
#==========================
#  Solaris
#
# For Solaris, BSD should not be replaced by UNIX100.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -DEPD_BIG_ENDIAN
# Gcc 2.8.1 or higher on Ultrasparc.
#XCFLAGS	= -mcpu=ultrasparc -DHAVE_IEEE_754 -DUNIX100 -DEPD_BIG_ENDIAN
# For Solaris 2.5 and higher, optimized code with /usr/bin/cc or CC.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -xO5 -native -dalign -DEPD_BIG_ENDIAN
# On IA platforms, -dalign is not supported and causes warnings.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -xO5 -native
# Recent Sun compilers won't let you use -native on old Ultras.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -xO5 -dalign -xlibmil -DEPD_BIG_ENDIAN
# For Solaris 2.4, optimized code with /usr/bin/cc.
#XCFLAGS	= -DHAVE_IEEE_754 -DUNIX100 -xO4 -dalign -DEPD_BIG_ENDIAN
# For Solaris 2.5 and higher, optimized code with /usr/ucb/cc.
#XCFLAGS	= -DHAVE_IEEE_754 -DBSD -xO5 -native -dalign -DEPD_BIG_ENDIAN
#XCFLAGS	= -DHAVE_IEEE_754 -DBSD -xO5 -dalign -xlibmil -DEPD_BIG_ENDIAN
# For Solaris 2.4, optimized code with /usr/ucb/cc.
#XCFLAGS	= -DHAVE_IEEE_754 -DBSD -xO4 -dalign -DEPD_BIG_ENDIAN
#
#==========================
#  DEC Alphas running Digital Unix
#
# For DEC Alphas either -ieee_with_inexact or -ieee_with_no_inexact is
# needed. If you use only BDDs, -ieee_with_no_inexact is enough.
# In the following, we consider three different compilers:
# - the old native compiler (the one of MIPS ancestry that produces u-code);
# - the new native compiler;
# - gcc
# On the Alphas, gcc (as of release 2.7.2) does not support 32-bit pointers
# and IEEE 754 floating point arithmetic. Therefore, for this architecture
# only, the native compilers provide a substatial advantage.
# With the native compilers, specify -xtaso for 32-bit pointers.
# Do not use -xtaso_short because explicit reference to stdout and stderr
# does not work with this option. (Among other things.)
# Notice that -taso must be included in LDFLAGS for -xtaso to work.
# Given the number of possible choices, only some typical configurations
# are proposed here.
#
# Old native compiler for the Alphas; 64-bit pointers.
#XCFLAGS	= -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
# Old native compiler for the Alphas; 32-bit pointers.
#XCFLAGS	= -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -xtaso -DSIZEOF_LONG=8
# New native compiler for the Alphas; 64-bit pointers.
#XCFLAGS	= -g3 -O4 -std -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
# New native compiler for the Alphas; 32-bit pointers.
#XCFLAGS	= -g3 -O4 -std -DBSD -DHAVE_IEEE_754 -ieee_with_no_inexact -tune host -xtaso -DSIZEOF_LONG=8
# gcc for the Alphas: compile without HAVE_IEEE_754.
#XCFLAGS	= -DBSD -DSIZEOF_VOID_P=8 -DSIZEOF_LONG=8
#
#==========================
#
#  IBM RS6000
#
# For the IBM RS6000 -qstrict is necessary when specifying -O3 with cc.
#XCFLAGS	= -DBSD -DHAVE_IEEE_754 -DEPD_BIG_ENDIAN -O3 -qstrict
#
#==========================
#
#  HP-UX
#
# I haven't figured out how to enable IEEE 754 on the HPs I've tried...
# For HP-UX using gcc.
#XCFLAGS	= -DUNIX100 -DEPD_BIG_ENDIAN
# For HP-UX using c89.
#XCFLAGS	= +O3 -DUNIX100 -DEPD_BIG_ENDIAN
#
#==========================
#
#  Windows 95/98/NT/XP/Vista/7 with Cygwin tools
#
# The value of RLIMIT_DATA_DEFAULT should reflect the amount of
# available memory (expressed in bytes).
# Recent versions of cygwin have getrlimit, but the datasize limit
# cannot be set.
#XCFLAGS	= -mtune=native -malign-double -DHAVE_IEEE_754 -DHAVE_GETRLIMIT=0 -DRLIMIT_DATA_DEFAULT=268435456
#
#==========================
#


# Define the level of self-checking and verbosity of the CUDD package.
#DDDEBUG = -DDD_DEBUG -DDD_VERBOSE -DDD_STATS -DDD_CACHE_PROFILE -DDD_UNIQUE_PROFILE -DDD_COUNT
DDDEBUG	=

# Define the level of self-checking and verbosity of the MTR package.
#MTRDEBUG = -DMTR_DEBUG
MTRDEBUG =

# Loader options.
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

# Define PURE as purify to link with purify.
# Define PURE as quantify to link with quantify.
# Remember to compile with -g if you want line-by-line info with quantify.
PURE =
#PURE	= purify
#PURE	= quantify

# Define EXE as .exe for MS-DOS and derivatives.  Not required by recent
# versions of cygwin.
EXE	=
#EXE	= .exe

# End of the configuration section.
#---------------------------------------------------------------------------

MFLAG   = -DMNEMOSYNE
MNEMLIB	= ../mnemosyne/libmnem.a

DDWDIR	= .
IDIR	= $(DDWDIR)/include
INCLUDE = -I$(IDIR)

BDIRS	= cudd dddmp mtr st util epd
DIRS	= $(BDIRS) nanotrav

#------------------------------------------------------------------------

.PHONY : build
.PHONY : nanotrav
.PHONY : check_leaks
.PHONY : optimize_dec
.PHONY : testcudd
.PHONY : libobj
.PHONY : testobj
.PHONY : testdddmp
.PHONY : testmtr
.PHONY : lint
.PHONY : all
.PHONY : clean
.PHONY : distclean
.PHONY : TAGS


build:
	sh ./setup.sh
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )\
	done

nanotrav: build

check_leaks:
	sh ./setup.sh
	@for dir in mnemosyne $(DIRS); do \
		(cd $$dir; \
		echo Making $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG=$(MFLAG) MNEMLIB=$(MNEMLIB) ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" EXE="$(EXE)" )\
	done

optimize_dec:
	sh ./setup.sh
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) XCFLAGS="$(XCFLAGS)" LDFLAGS="$(LDFLAGS)" optimize_dec )\
	done

lint:
	sh ./setup.sh
	@for dir in $(DIRS) obj; do \
		(cd $$dir; \
		echo Making lint in $$dir ...; \
		${MAKE} CC=$(CC) lint )\
	done

tags:
	sh ./setup.sh
	@for dir in $(DIRS) obj; do \
		(cd $$dir; \
		echo Making tags in $$dir ...; \
		${MAKE} CC=$(CC) tags )\
	done

all:
	sh ./setup.sh
	@for dir in $(DIRS); do \
		(cd $$dir; \
		echo Making all in $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" all )\
	done

testcudd:
	sh ./setup.sh
	@for dir in util st mtr epd; do \
		(cd $$dir; \
		echo Making $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )\
	done
	@(cd cudd; \
	echo Making testcudd ...; \
	${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" testcudd$(EXE) )

objlib:
	sh ./setup.sh
	@for dir in $(BDIRS); do \
		(cd $$dir; \
		echo Making $$dir ...; \
		${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )\
	done
	@(cd obj; \
	echo Making obj ...; \
	${MAKE} CXX=$(CXX) CXXFLAGS=$(CXXFLAGS) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" )

testobj: objlib
	@(cd obj; \
	echo Making testobj ...; \
	${MAKE} CXX=$(CXX) CXXFLAGS=$(CXXFLAGS) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" testobj$(EXE) )

testdddmp: build
	@(cd dddmp; \
	echo Making testdddmp ...; \
	${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" testdddmp$(EXE) )

testmtr: build
	@(cd mtr; \
	echo Making testmtr ...; \
	${MAKE} CC=$(CC) RANLIB=$(RANLIB) MFLAG= MNEMLIB= ICFLAGS="$(ICFLAGS)" XCFLAGS="$(XCFLAGS)" DDDEBUG="$(DDDEBUG)" MTRDEBUG="$(MTRDEBUG)" LDFLAGS="$(LDFLAGS)" PURE="$(PURE)" EXE="$(EXE)" testmtr$(EXE) )

TAGS:
	etags */*.{h,c,hh,cc}

clean:
	@for dir in mnemosyne $(DIRS) obj; do	\
	    (cd $$dir;	\
	     echo Cleaning $$dir ...; \
	     ${MAKE} -s clean	) \
	done

distclean:
	@for dir in mnemosyne $(DIRS) obj; do	\
	    (cd $$dir;	\
	     echo Cleaning $$dir ...; \
	     ${MAKE} -s EXE="$(EXE)" distclean	) \
	done
	rm -f TAGS 
	sh ./shutdown.sh
