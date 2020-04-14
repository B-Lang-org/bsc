PWD:=$(shell pwd)
TOP:=$(PWD)/../..

include $(TOP)/platform.mk

TMPDIR=/tmp

# -----
# System tools

INSTALL ?= install

RM = rm -f
LN = ln -sf

FIND = find

# -----
# Options

# Set this to 1 if the source files are not in Git or the Git tool
# is not available.  The variable is used by "update-build-version.sh"
# which will not try running Git if the value is 1.
#
NOGIT ?= 0
export NOGIT

# With NOGIT=1, the build version will be update to a null value.
# If you want to pre-create the file and avoid overwriting it,
# then set this variable to 1.
#
NOUPDATEBUILDVERSION ?= 0
export NOUPDATEBUILDVERSION

# -----
# Paths and environment

# PREFIX is where things are installed
PREFIX?=$(TOP)/inst
BINDIR=$(PREFIX)/bin

# Top-level of where intermediate GHC files are stored
BUILDDIR=$(TOP)/build

# Parsec
PARSEC_HS = ../Parsec

# STP
STP_HS = ../vendor/stp/include_hs
STP_INC_FLAGS = -I../vendor/stp/include
STP_LIB_FLAGS = -L../vendor/stp/lib -lstp

# Yices
YICES_HS = ../vendor/yices/include_hs
YICES_INC_FLAGS = -I../vendor/yices/include
YICES_LIB_FLAGS = -L../vendor/yices/lib -lyices

# HTCL
HTCL_HS = ../vendor/htcl
HTCL_INC_FLAGS = -L$(HTCL_HS)
HTCL_LIB_FLAGS = -lhtcl

# TCL/TK version
ifeq ($(OSTYPE), Darwin)
# Have Makefile avoid Homebrew's install of tcl on Mac
TCLSH=/usr/bin/tclsh
else
TCLSH=tclsh
endif
TCLTK_VER = $(shell echo 'catch { puts [info tclversion]; exit 0}; exit 1' | $(TCLSH) || echo fail)
ifeq ($(TCLTK_VER),fail)
$(error TCL version check failed)
endif

# TCL/TK include flags
TCLTK_INC_FLAGS = $(shell pkg-config --silence-errors --cflags-only-I tcl tk || echo -I/usr/include/tcl)
ifeq ($(OSTYPE), Darwin)
TCLTK_INC_FLAGS += -I$(shell xcrun --show-sdk-path)/System/Library/Frameworks/Tk.framework/Headers
endif

# TCL library flags
TCL_LIB_FLAGS = -ltcl$(TCLTK_VER)

# TK library flags
TK_LIB_FLAGS = -ltk$(TCLTK_VER) $(shell pkg-config --libs x11 fontconfig xft)

# -----
# GHC

GHC ?= ghc
GHCJOBS ?= 1

GHCVERSION=$(shell $(GHC) --version | head -1 | egrep -o "[0-9]+\.[0-9]+\.[0-9]" )

## Extract the major, minor and patch version numbers
GHCMAJOR=$(shell echo $(GHCVERSION) | cut -d. -f1)
GHCMINOR=$(shell echo $(GHCVERSION) | cut -d. -f2)
GHCPATCH=$(shell echo $(GHCVERSION) | cut -d. -f3)

# Set version-specific GHC flags
#
#$(info Building with GHC $(GHCMAJOR).$(GHCMINOR))
ifeq ($(GHCMAJOR),8)

GHC += -Wtabs

GHCEXTRAPKGS =-package syb -package integer-gmp
GHCPROFAUTO = -fprof-auto

# end ifeq ($(GHCMAJOR),8)
else
ifeq ($(GHCMAJOR),7)

# Make sure that all calls to GHC 7.0.4 use this flag to suppress
# messages that were accidentally checked in to that revision
GHC += -dno-debug-output

GHC += -fwarn-tabs

GHCEXTRAPKGS =-package syb -package integer-gmp

# In 7.4, the auto annotations flag changed
GHCMINORGTE4 := $(shell expr $(GHCMINOR) \>= 4)
ifeq ($(GHCMINORGTE4),1)
GHCPROFAUTO = -fprof-auto
else
GHCPROFAUTO = -auto-all
endif

# end ifeq ($(GHCMAJOR),7)
else
# Not GHC 8 or 7
$(error Unrecognized GHC major version: $(GHCMAJOR))
endif
endif

PACKAGES = \
	-package base \
	-package containers \
	-package array \
	-package mtl \
	-package unix \
	-package regex-compat \
	-package bytestring \
	-package directory \
	-package process \
	-package filepath \
	-package time \
	-package old-time \
	-package old-locale \
	-package split \
	$(GHCEXTRAPKGS)

# GHC can compile either a single file (use GHCCOMPILEFLAGS) or
# in make mode where it follows dependencies (use GHCMAKEFLAGS).
#
# The make flags do not include "-o" because bluetcl and bluewish
# are compiled in two steps and the first step doesn't have that option.
# So all users of GHCMAKEFLAGS have to include "-o" themselves.
GHCMAKEFLAGS = --make $@ -j$(GHCJOBS)
GHCCOMPILEFLAGS = -o $@ -c $<

# On Mac OS, we'll need to update the dylib location,
# so linking needs to pad the field so that there's room to overwrite
ifeq ($(OSTYPE), Darwin)
GHC += -optl -headerpad_max_install_names
endif

# flags for the haskell compiler RTS
GHCRTSFLAGS ?= +RTS -M3G -A128m -RTS

# flags for the haskell compile
GHCINCLUDES =  \
	-iGHC -iGHC/posix -iLibs \
	-i$(PARSEC_HS) \
	-i$(STP_HS) \
	-i$(YICES_HS) \
	-i$(HTCL_HS)
GHCTMP = '-tmpdir $(TMPDIR)'
FVIA ?= -fasm
GHCFLAGS = \
	-hide-all-packages \
	$(FVIA) \
	-Wall \
	-fno-warn-orphans \
	-fno-warn-name-shadowing \
	-fno-warn-unused-matches \
	$(PACKAGES) \
	$(GHCINCLUDES) \
	$(GHCTMP) \

# GHC will recompile a module if certain flags (such as -I) have changed.
# To avoid recompiling the shared modules each time we compile a tool,
# we provide the -I flags for all tools in every use of GHC.
GHCFLAGS += \
	$(STP_INC_FLAGS) \
	$(YICES_INC_FLAGS) \
	$(HTCL_INC_FLAGS) \
	$(TCLTK_INC_FLAGS) \

ifeq ($(OSTYPE), Linux)
# Some GHC installations may fail to include this automatically,
# and it's benign to include otherwise
GHCFLAGS += -lpthread
endif

GHCMAJORGTE7 := $(shell expr $(GHCMAJOR) \>= 7)
ifeq ($(GHCMAJORGTE7),1)
GHCFLAGS += -rtsopts
endif

# Use -O2, except with GHC 7.7 which is very slow with -O2
# (and ASchedule.hs and bsc.hs don't compile at that level)
ifeq ($(GHCMAJOR),7)
GHCMINORGTE7 := $(shell expr $(GHCMINOR) \>= 7)
ifeq ($(GHCMINORGTE7),1)
GHCOPTLEVEL ?= -O1
else
GHCOPTLEVEL ?= -O2
endif
else
GHCOPTLEVEL ?= -O2
endif
GHCOPTFLAGS = $(GHCOPTLEVEL) $(GHCFLAGS)

GHCPROF = -prof $(GHCPROFAUTO) '-osuf p_o' '-hisuf p_hi'
GHCOPTPROFFLAGS = $(GHCOPTFLAGS) $(GHCPROF)

GHCDEBUG = -dcore-lint -debug '-osuf d_o' '-hisuf d_hi'
GHCOPTDEBUGFLAGS = $(GHCOPTFLAGS) $(GHCDEBUG)

# -----
# Targets

#clean build has no BuildVersion.hs
SOURCES_WO_EXTRA_BUILDVERSION = \
	*.hs *.lhs \
	Parser/*.hs Parser/BSV/*.lhs Parser/Classic/*.hs \
	Libs/*.hs \
	GHC/*.hs GHC/posix/*.hs \
	$(PARSEC_HS)/*.hs \
	$(STP_HS)/*.hs \
	$(YICES_HS)/*.hs \
	$(HTCL_HS)/*.hs

SOURCES = BuildVersion.hs BuildSystem.hs $(SOURCES_WO_EXTRA_BUILDVERSION)

BSCEXES = bsc
TCLEXES = bluetcl bluewish
UTILEXES = bsc2bsv bsv2bsc dumpbo dumpba vcdcheck
SHOWRULESEXES = showrules

EXES = $(BSCEXES) $(TCLEXES) $(UTILEXES) $(SHOWRULESEXES)

# always depend on both sets of RTS hooks, but link only one in
EXTRAOBJNORMAL = rts_hooks.o
EXTRAOBJPROF = rts_hooks_prof.o
EXTRAOBJS = $(EXTRAOBJNORMAL) $(EXTRAOBJPROF)

.PHONY: all
all: $(EXES)

BuildVersion.hs:
	./update-build-version.sh

BuildSystem.hs:
	./update-build-system.sh

# Common among all targets
BUILDSTART = @echo $@ start `date`
BUILDDONE = @echo $@ done `date`; echo

PREBUILDCOMMAND = $(BUILDSTART); mkdir -p $(BUILDDIR)
BUILDCOMMAND = $(GHC) -hidir $(BUILDDIR) -odir $(BUILDDIR) -stubdir $(BUILDDIR)
POSTBUILDCOMMAND = $(BUILDDONE)

# While GHCFLAGS contains the sum of all -I flags for every tool
# (to avoid recompilation of modules because flags changed)
# we only provide the -L and -l flags for the specific tools that need them
# (to avoid creating binaries with unnecessary library requirements)
#
BSC_BUILDLIBS = \
	$(STP_LIB_FLAGS) \
	$(YICES_LIB_FLAGS) \

BLUETCL_BUILDLIBS = \
	$(BSC_BUILDLIBS) \
	$(TCL_LIB_FLAGS) \
	$(HTCL_LIB_FLAGS) \

BLUEWISH_BUILDLIBS = \
	$(BLUETCL_BUILDLIBS) \
	$(TK_LIB_FLAGS) \

# Choose prof/debug/normal based on environment variables
ifeq ($(BSC_BUILD),PROF)
$(info ----- Profiling build options -----)
BUILDFLAGS = $(GHCOPTPROFFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJPROF)
else
ifeq ($(BSC_BUILD),DEBUG)
$(info ----- Debug build options -----)
BUILDFLAGS = $(GHCOPTDEBUGFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
else
ifeq ($(BSC_BUILD),NOOPT)
$(info ----- Unoptimized build options -----)
BUILDFLAGS = $(GHCFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
else
$(info ----- Normal build options -----)
BUILDFLAGS = $(GHCOPTFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
endif
endif
endif

.PHONY: bsc
bsc: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
        # to force updating of BuildVersion/BuildSystem when necessary
	./update-build-version.sh
	./update-build-system.sh
	$(BUILDCOMMAND) -main-is Main_$@ \
		$(BUILDFLAGS) $(BSC_BUILDLIBS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: bsc2bsv
bsc2bsv: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: bsv2bsc
bsv2bsc: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: dumpbo
dumpbo: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: dumpba
dumpba: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: vcdcheck
vcdcheck: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: showrules
showrules: $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(EXTRAOBJ)
	$(POSTBUILDCOMMAND)

.PHONY: bluetcl
bluetcl: bluetcl.hs bluetcl_Main.hsc $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) $(BUILDFLAGS) -c $(EXTRAOBJ)
	$(BUILDCOMMAND) $(BUILDFLAGS) $(BLUETCL_BUILDLIBS) \
		-o $@ \
		-no-hs-main $(EXTRAOBJ) \
		-x c bluetcl_Main.hsc
	$(POSTBUILDCOMMAND)

BLUEWISHCP = cp -p bluetcl.hs bluewish.hs
BLUEWISHDIFF = diff -q bluetcl.hs bluewish.hs || $(BLUEWISHCP)

.PHONY: bluewish.hs
bluewish.hs: bluetcl.hs
	if test -f bluewish.hs; then $(BLUEWISHDIFF); else $(BLUEWISHCP); fi;

.PHONY: bluewish
bluewish: bluewish.hs bluewish_Main.hsc $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) $(BUILDFLAGS) -c $(EXTRAOBJ)
	$(BUILDCOMMAND) $(BUILDFLAGS) $(BLUEWISH_BUILDLIBS) \
		-o $@ \
		-no-hs-main $(EXTRAOBJ) \
		-x c bluewish_Main.hsc
	$(POSTBUILDCOMMAND)

# -----
# Install targets

.PHONY: install
install: $(BSCEXES) $(TCLEXES) install-bsc install-bluetcl

.PHONY: install-extra
install-extra: $(UTILEXES) $(SHOWRULESEXES) install-util install-showrules

# Until the need for BLUESPECDIR and LD_LIBRARY_PATH to be set is removed
# put the binaries in a "core" subdirectory and a wrapper script in "bin"
$(BINDIR)/core/%: %
	mkdir -p -m 755 $(BINDIR)/core
	$(INSTALL) -m 755 $(@F) $(BINDIR)/core/$(@F)

$(BINDIR)/%: wrapper.sh $(BINDIR)/core/%
	mkdir -p -m 755 $(BINDIR)
	$(INSTALL) -m 755 wrapper.sh $(BINDIR)/$(@F)

.PHONY: install-bsc
install-bsc: $(addprefix $(BINDIR)/,$(BSCEXES))
install-bsc: $(addprefix $(BINDIR)/core/,$(BSCEXES))

.PHONY: install-bluetcl
install-bluetcl: $(addprefix $(BINDIR)/,$(TCLEXES))
install-bluetcl: $(addprefix $(BINDIR)/core/,$(TCLEXES))

.PHONY: install-utils
install-utils: $(addprefix $(BINDIR)/,$(UTILEXES))
install-utils: $(addprefix $(BINDIR)/core/,$(UTILEXES))

.PHONY: install-showrules
install-showrules: $(addprefix $(BINDIR)/,$(SHOWRULESEXES))
install-showrules: $(addprefix $(BINDIR)/core/,$(SHOWRULESEXES))

# ----
# Other targets

tags:   *hs */*hs bluewish.hs
	$(FIND) . $(PARSEC_HS) $(STP_HS) $(YICES_HS) $(HTCL_HS) \
		-type f -name \*hs | xargs hasktags
	mv tags tags.tmpfile
	sort tags.tmpfile > tags
	$(RM) tags.tmpfile

# -----
# Clean targets

.PHONY: clean
clean:
	$(RM) -rf $(EXES) $(BUILDDIR)
	$(RM) -f bluetcl_stub.[ch] bluewish_stub.[ch] bluewish.hs

.PHONY: full_clean
full_clean: clean
	$(RM) -f BuildSystem.hs BuildVersion.hs
	$(RM) -f rts_hooks.o rts_hooks_prof.o
	$(RM) tags TAGS

# -----
