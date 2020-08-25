TOP=../../../../..
include $(TOP)/platform.mk

YICES_INST = ../yices2-inst

YICES_SRC = ../yices2/src

YICES_SRC_INC = $(YICES_SRC)/include

# -------------------------

CCFLAGS	=  -c -Wall -fPIC
USERCCFLAGS ?=

LIBNAME = libyices
MAJOR = 2
MINOR = 6
VER = $(MAJOR).$(MINOR)
SUBVER = stub

SRC = yices.c
HEADERS = \
	$(YICES_SRC_INC)/yices.h \
	$(YICES_SRC_INC)/yices_types.h \
	$(YICES_SRC_INC)/yices_limits.h \

# -------------------------

FULLVER = $(VER).$(SUBVER)

SNAME = $(LIBNAME).so.$(VER)
FULLNAME = $(LIBNAME).so.$(FULLVER)
OBJECTS = $(addsuffix .o, $(basename $(SRC)))

# -------------------------

IPATH   = -I$(YICES_SRC_INC)

AR	= ar -r
RM	= rm -rf

# BSD cp does not have the -d flag
ifneq ($(OSTYPE), Linux)
CP	= cp -Rf
else
CP	= cp -df
endif

.SUFFIXES: .o .c

# Flags for creating a shared library
ifeq ($(OSTYPE), Darwin)
SHAREDFLAG = -dynamiclib
SONAMEFLAG = -install_name
else
SHAREDFLAG = -shared
SONAMEFLAG = -soname
endif

# -------------------------

all: $(FULLNAME)
	ln -sf $< $(SNAME)
	ln -sf $< $(LIBNAME).so


$(FULLNAME): $(OBJECTS)
	$(CC) $(SHAREDFLAG) -Wl,$(SONAMEFLAG),$(SNAME) -o $@ $<


$(LIBNAME).a:	$(OBJECTS)
	$(AR) $@ $^


%.o:	%.c $(HEADERS)
	$(CC) $(CCFLAGS) $(USERCCFLAGS) $(IPATH) -o $@ $<

install: all
	mkdir -p $(YICES_INST)/lib
	$(CP) $(FULLNAME) $(SNAME) $(LIBNAME).so  $(YICES_INST)/lib/
	mkdir -p $(YICES_INST)/include
	$(CP) $(HEADERS) $(YICES_INST)/include/

.PHONY: clean full_clean

clean:
	$(RM) *.o $(FULLNAME) $(SNAME) $(LIBNAME).so

full_clean: clean
	$(RM) $(YICES_INST)/lib
	$(RM) $(YICES_INST)/include

# -------------------------
