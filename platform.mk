## This Makefile fragment can be included in Makefiles throughout this repo
## to ensure that the following variables have canonical values:
##
##   MACHTYPE = x86_64, i386, i486, i586, i686
##   OSTYPE = Linux, Darwin
##
## It can also add values for the following variables:
##
##   CFLAGS
##   CXXFLAGS
##
## It requires the following variables be set:
##
##   TOP = the location of this Makefile at the top of the repo

## --------------------
## Setup MACHTYPE

MACHTYPE = $(shell $(TOP)/platform.sh machtype)
export MACHTYPE

ifneq ($(MACHTYPE), $(findstring $(MACHTYPE), x86_64 i386 i486 i586 i686 ppc64le aarch64 armv7l))
$(error MACHTYPE environment not recognized: $(MACHTYPE))
endif

## --------------------
## Setup OSTYPE

OSTYPE = $(shell $(TOP)/platform.sh ostype)
export OSTYPE

ifneq ($(OSTYPE), $(findstring $(OSTYPE), Linux Darwin Freebsd))
$(error OSTYPE environment not recognized: $(OSTYPE))
endif

## --------------------
## Setup common C/C++ flags

ifeq ($(MACHTYPE), $(findstring $(MACHTYPE), i386 i486 i586 i686))
# Set -m32 to be sure that CC is generating 32-bit
CFLAGS ?= -m32
CXXFLAGS ?= -m32
else
ifeq ($(MACHTYPE), $(findstring $(MACHTYPE), x86_64))
# Set -m64 to be sure that CC is generating 64-bit
CFLAGS ?= -m64
CXXFLAGS ?= -m64
else
ifeq ($(MACHTYPE), $(findstring $(MACHTYPE), ppc64le aarch64 armv7l))
else
$(error MACHTYPE environment not recognized: $(MACHTYPE))
endif
endif
endif
export CFLAGS
export CXXFLAGS

## --------------------
## Set up the TCL shell and include paths
ifneq ($(WANT_TCL),)
TCLSH = $(shell $(TOP)/platform.sh tclsh)
ifeq ($(TCLSH), )
$(error Unable to find tclsh)
endif
$(info Using tclsh: $(TCLSH))
TCL_INC_FLAGS = $(shell $(TOP)/platform.sh tclinc)
ifeq ($(TCL_INC_FLAGS), )
$(error Unable to find tcl include directory)
endif
$(info Using tcl include flags: $(TCL_INC_FLAGS))
TCL_LIB_FLAGS = $(shell $(TOP)/platform.sh tcllibs)
ifeq ($(TCL_LIB_FLAGS), )
$(error Unable to find tcl library flags)
endif
$(info Using tcl library flags: $(TCL_LIB_FLAGS))
endif
