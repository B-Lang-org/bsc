TOP:=$(shell pwd)/../..
WANT_TCL=yes

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
BUILDDIR=$(TOP)/build/comp

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
# HTcl.hs needs macro definitions
HTCL_INC_FLAGS += $(addprefix -D,$(TCL_DEFS))

# -----
# GHC

GHC ?= ghc
GHCJOBS ?= 1

GHCVERSION=$(shell $(GHC) --version | head -1 | grep -Eo "[0-9]+\.[0-9]+\.[0-9]" )
$(info Building with GHC $(GHCVERSION))

## Extract the major, minor and patch version numbers
GHCMAJOR=$(shell echo $(GHCVERSION) | cut -d. -f1)
GHCMINOR=$(shell echo $(GHCVERSION) | cut -d. -f2)
GHCPATCH=$(shell echo $(GHCVERSION) | cut -d. -f3)

# Check that the GHC version is supported
# and set version-specific GHC flags
#
#$(info Building with GHC $(GHCMAJOR).$(GHCMINOR))
ifeq ($(GHCMAJOR),9)

# Warn about newer versions that are not yet supported
GHCMINORGT10 := $(shell expr $(GHCMINOR) \> 10)
ifeq ($(GHCMINORGT10),1)
$(warning Unsupported GHC 9 minor version: $(GHCMINOR))
endif

# Work around a bug in GHC 9.2.1 (see GHC issue 20639)
ifeq ($(GHCVERSION),9.2.1)
$(warning Building unoptimized to work around a bug in GHC 9.2.1)
GHCOPTLEVEL ?= -O0
endif

GHC += -Wtabs -fmax-pmcheck-models=800

# end ifeq ($(GHCMAJOR),9)
else
ifeq ($(GHCMAJOR),8)

GHC += -Wtabs

# end ifeq ($(GHCMAJOR),8)
else
ifeq ($(GHCMAJOR),7)

# Versions before 7.10 are not supported
GHCMINORLT10 := $(shell expr $(GHCMINOR) \< 10)
ifeq ($(GHCMINORLT10),1)
$(error Unsupported GHC 7 minor version: $(GHCMINOR))
endif

GHC += -fwarn-tabs

# end ifeq ($(GHCMAJOR),7)
else
# Not GHC 7, 8, or 9
$(error Unsupported GHC major version: $(GHCMAJOR))
endif
endif
endif

GHCPROFAUTO = -fprof-auto

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
	-package syb \
	-package integer-gmp \
	-package text \
	-package deepseq \
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
GHCRTSFLAGS ?= +RTS -M4G -A128m -RTS

# flags for the haskell compile
GHCINCLUDES =  \
	-iGHC/posix -iLibs \
	-i$(PARSEC_HS) \
	-i$(STP_HS) \
	-i$(YICES_HS) \
	-i$(HTCL_HS)
GHCTMP = '-tmpdir $(TMPDIR)'
# Default RTS flags for programs built with a Haskell main
# 256MB heap, 10MB stack, 1 second interval between heap profiles
# If you modify this, also update rts_opts in ../vendor/htcl/haskell.c
RTSFLAGS = "-with-rtsopts=-H256m -K10m -i1"
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
	$(TCL_INC_FLAGS) \

ifeq ($(OSTYPE), Linux)
# Some GHC installations may fail to include this automatically,
# and it's benign to include otherwise
GHCFLAGS += -lpthread
endif

# Get Haskell runtime to parse and filter +RTS ... -RTS args
# from command line arguments at program start
RTSFLAGS += -rtsopts

# Use -O2, except when a particular GHC version has a bug that
# needs working around, in which case, use the value set earlier
# for that version
GHCOPTLEVEL ?= -O2

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
	GHC/posix/*.hs \
	$(PARSEC_HS)/*.hs \
	$(STP_HS)/*.hs \
	$(YICES_HS)/*.hs \
	$(HTCL_HS)/*.hs

SOURCES = BuildVersion.hs BuildSystem.hs $(SOURCES_WO_EXTRA_BUILDVERSION)

BSCEXES = bsc
TCLEXES = bluetcl
UTILEXES = bsc2bsv bsv2bsc dumpbo dumpba vcdcheck
SHOWRULESEXES = showrules

EXES = $(BSCEXES) $(TCLEXES) $(UTILEXES) $(SHOWRULESEXES)

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

# Choose prof/debug/normal based on environment variables
ifeq ($(BSC_BUILD),PROF)
$(info ----- Profiling build options -----)
BUILDFLAGS = $(GHCOPTPROFFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
else
ifeq ($(BSC_BUILD),DEBUG)
$(info ----- Debug build options -----)
BUILDFLAGS = $(GHCOPTDEBUGFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
else
ifeq ($(BSC_BUILD),NOOPT)
$(info ----- Unoptimized build options -----)
BUILDFLAGS = $(GHCFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
else
$(info ----- Normal build options -----)
BUILDFLAGS = $(GHCOPTFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
endif
endif
endif

.PHONY: bsc
bsc: $(SOURCES)
	$(PREBUILDCOMMAND)
        # to force updating of BuildVersion/BuildSystem when necessary
	./update-build-version.sh
	./update-build-system.sh
	$(BUILDCOMMAND) -main-is Main_$@ \
		$(BUILDFLAGS) $(RTSFLAGS) $(BSC_BUILDLIBS)
	$(POSTBUILDCOMMAND)

.PHONY: bsc2bsv
bsc2bsv: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

.PHONY: bsv2bsc
bsv2bsc: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

.PHONY: dumpbo
dumpbo: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

.PHONY: dumpba
dumpba: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

.PHONY: vcdcheck
vcdcheck: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

.PHONY: showrules
showrules: $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) -main-is Main_$@ $(BUILDFLAGS) $(RTSFLAGS)
	$(POSTBUILDCOMMAND)

# bluetcl is built in two steps:
# 1. Build BlueTcl module using -c to emit .hi/.o files, and also the
#    BlueTcl_stub.h reqired by bluetcl_Main.hsc in the next action
# 2. Link BlueTcl with a custom C main that #includes BlueTcl_stub.h
.PHONY: bluetcl
bluetcl: bluetcl.hs bluetcl_Main.hsc $(SOURCES)
	$(PREBUILDCOMMAND)
	$(BUILDCOMMAND) $(BUILDFLAGS) -c
	$(BUILDCOMMAND) $(BUILDFLAGS) $(BLUETCL_BUILDLIBS) \
		-o $@ \
		-no-hs-main \
		-x c bluetcl_Main.hsc
	$(POSTBUILDCOMMAND)

# -----
# Install targets

.PHONY: install
install: $(BSCEXES) $(TCLEXES) install-bsc install-bluetcl

.PHONY: install-extra
install-extra: $(UTILEXES) $(SHOWRULESEXES) install-utils install-showrules

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

.PHONY: full_clean
full_clean: clean
	$(RM) -f BuildSystem.hs BuildVersion.hs
	$(RM) tags TAGS

# -----
