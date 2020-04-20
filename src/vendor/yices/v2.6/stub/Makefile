TOP=../../../../..
include $(TOP)/platform.mk

YICES_INST = ../yices2-inst

YICES_SRC = ../yices2/src

YICES_SRC_INC = $(YICES_SRC)/include

# -------------------------

CCFLAGS	=  -c -Wall -fPIC
USERCCFLAGS ?=

LIBNAME = libyices
VER = 2
SUBVER = stub

SRC = yices.c
HEADERS = \
	$(YICES_SRC_INC)/yices.h \
	$(YICES_SRC_INC)/yices_types.h \
	$(YICES_SRC_INC)/yices_limits.h \

# -------------------------

FULLVER = $(VER).$(SUBVER)

ifeq ($(OSTYPE), Darwin)
SNAME = $(LIBNAME).$(VER).dylib
FULLNAME = $(LIBNAME).$(FULLVER).dylib
NOVERNAME = $(LIBNAME).dylib
else
SNAME = $(LIBNAME).so.$(VER)
FULLNAME = $(LIBNAME).so.$(FULLVER)
NOVERNAME = $(LIBNAME).so
endif
OBJECTS = $(addsuffix .o, $(basename $(SRC)))

# -------------------------

IPATH   = -I$(YICES_SRC_INC)

AR	= ar -r
RM	= rm -rf

# BSD cp does not have the -d flag
ifeq ($(OSTYPE), Darwin)
CP	= cp -Rf
else
CP	= cp -df
endif

.SUFFIXES: .o .c

# Flags for creating a shared library
ifeq ($(OSTYPE), Darwin)
SHAREDFLAG = -dynamiclib
SONAMEFLAG = -install_name
# When linked into a binary, use this 'install_name'. @rpath makes library
# be loaded relative to the rpath baked into the binary.
INAME = @rpath/$(SNAME)
else
SHAREDFLAG = -shared
SONAMEFLAG = -soname
INAME = $(SNAME)
endif

# -------------------------

all: $(FULLNAME)
	ln -sf $< $(SNAME)
	ln -sf $< $(NOVERNAME)


$(FULLNAME): $(OBJECTS)
	$(CC) $(SHAREDFLAG) -Wl,$(SONAMEFLAG),$(INAME) -o $@ $<


$(LIBNAME).a:	$(OBJECTS)
	$(AR) $@ $^


%.o:	%.c $(HEADERS)
	$(CC) $(CCFLAGS) $(USERCCFLAGS) $(IPATH) -o $@ $<

install: all
	mkdir -p $(YICES_INST)/lib
	$(CP) $(FULLNAME) $(SNAME) $(NOVERNAME)  $(YICES_INST)/lib/
	mkdir -p $(YICES_INST)/include
	$(CP) $(HEADERS) $(YICES_INST)/include/

.PHONY: clean full_clean

clean:
	$(RM) *.o $(FULLNAME) $(SNAME) $(NOVERNAME)

full_clean: clean
	$(RM) $(YICES_INST)/lib
	$(RM) $(YICES_INST)/include

# -------------------------
