# $Id$
#
# util -- miscellaneous utility routines
#---------------------------------------------------------------------------
.SUFFIXES: .c .o .u

#CC	= gcc
RANLIB	= ranlib

FLAGS	= -DUNIX
MFLAG   =
ICFLAGS = -g
CFLAGS  = $(ICFLAGS) $(MFLAG) $(XCFLAGS)

LINTFLAGS = -u -n

# this is to create the lint library
LINTSWITCH = -o

P	= util
PSRC	= cpu_time.c cpu_stats.c safe_mem.c strsav.c texpand.c \
	  ptime.c prtime.c pipefork.c pathsearch.c stub.c datalimit.c
POBJ	= $(PSRC:.c=.o)
PUBJ	= $(PSRC:.c=.u)
PHDR	= util.h

WHERE	= ..
INCLUDE = $(WHERE)/include

lib$(P).a: $(POBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.o: $(PHDR)
	$(CC) -c $< -I$(INCLUDE) $(FLAGS) $(CFLAGS)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.u: $(PHDR)
	cc -j $< -I$(INCLUDE) $(FLAGS) $(XCFLAGS)

# if the header files change, recompile
$(POBJ): $(PHDR)
$(PUBJ): $(PHDR)

lint: llib-l$(P).ln

llib-l$(P).ln: $(PSRC) $(PHDR)
	lint $(LINTFLAGS) $(LINTSWITCH)$(P) -I$(INCLUDE) $(PSRC)

tags: $(PSRC) $(PHDR)
	ctags $(PSRC) $(PHDR)

all: lib$(P).a lib$(P).b llib-l$(P).ln tags

clean:
	rm -f *.o *.u core *.warnings

distclean: clean
	rm -f lib$(P).a lib$(P).b llib-l$(P).ln tags *.bak *~ .pure
