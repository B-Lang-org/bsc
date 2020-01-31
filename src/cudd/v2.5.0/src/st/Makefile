# $Id: Makefile,v 1.3 2004/01/01 06:53:06 fabio Exp fabio $
#
# st -- hash table package
#---------------------------------------------------------------------------
.SUFFIXES: .c .o .u

#CC	= gcc
RANLIB	= ranlib

MFLAG	=
ICFLAGS = -g -O6 -Wall
CFLAGS  = $(ICFLAGS) $(MFLAG) $(XCFLAGS)

LINTFLAGS = -u -n

# this is to create the lint library
LINTSWITCH = -o

P	= st
PSRC	= st.c
PHDR	= st.h
POBJ	= $(PSRC:.c=.o)
PUBJ	= $(PSRC:.c=.u)

WHERE	= ..
INCLUDE = $(WHERE)/include

#---------------------------

lib$(P).a: $(POBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.o: $(PHDR)
	$(CC) -c $< -I$(INCLUDE) $(CFLAGS)

optimize_dec: lib$(P).b

lib$(P).b: $(PUBJ)
	ar rv $@ $?
	$(RANLIB) $@

.c.u: $(PSRC) $(PHDR)
	cc -j $< -I$(INCLUDE) $(XCFLAGS)

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
	rm -f *.o *.u .pure *.warnings

distclean: clean
	rm -f lib*.a lib$(P).b llib-l$(P).ln tags *~ *.bak *.qv *.qx
