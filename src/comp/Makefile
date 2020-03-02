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

#for compiler-script.sh
export CC

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

# Tcl
TCL_VER   = $(shell echo 'puts [info tclversion]' | tclsh)
ITCL_VER  = $(shell echo 'puts [package require Itcl]' | tclsh)
TCL_HS    = ../vendor/htcl
TCL_ARGS  = -L$(TCL_HS) $(shell pkg-config --silence-errors --cflags-only-I tcl tk || echo -I/usr/include/tcl)
TCL_LIBS  = -ltcl$(TCL_VER) -ltclstub$(TCL_VER) \
            -ltk$(TCL_VER) -ltkstub$(TCL_VER) \
            -litcl$(ITCL_VER) -litclstub$(ITCL_VER) -lhtcl

# STP
STP_HS      = ../vendor/stp/include_hs
STP_ARGS = -I../vendor/stp/include -L../vendor/stp/lib
STP_LIBS = -lstp

# Yices
YICES_HS      = ../vendor/yices/include_hs
YICES_ARGS = -I../vendor/yices/include -L../vendor/yices/lib
YICES_LIBS = -lyices

# Libs which are only needed to build bsc/bluetcl
# and which shouldn't be used to build other Haskell binaries
BSCBUILDLIBS = \
	$(TCL_LIBS) \
	$(STP_LIBS) \
	$(YICES_LIBS) \

EXTRAWISHLIBS = $(shell pkg-config --libs fontconfig xft)

WISHFLAGS = -litkstub$(ITCL_VER) -litk$(ITCL_VER) $(shell pkg-config --libs x11)
WISHFLAGS += $(EXTRAWISHLIBS)

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

# Several modules require more iterations
GHC += -fmax-pmcheck-iterations=6000000

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
GHCRTSFLAGS = +RTS -M3G -A128m -RTS

# flags for the haskell compile
GHCINCLUDES =  \
	-iGHC -iGHC/posix -iLibs \
	-i$(PARSEC_HS) \
	-i$(STP_HS) \
	-i$(YICES_HS) \
	-i$(TCL_HS)
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
	$(TCL_ARGS) \
	$(STP_ARGS) \
	$(YICES_ARGS) \
	'-pgma ./compiler-script.sh' \
	'-pgmc ./compiler-script.sh' \
	'-pgml ./compiler-script.sh'

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
	$(TCL_HS)/*.hs

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

# Choose prof/debug/normal based on environment variables
ifeq ($(BSC_BUILD),PROF)
$(info ----- Profiling build options -----)
BUILDFLAGS = $(GHCOPTPROFFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJPROF)
TCLSTUB = $(TCLSTUBPROF)
TCLCLEAN = $(TCLCLEANPROF)
WISHSTUB = $(WISHSTUBPROF)
WISHCLEAN = $(WISHCLEANPROF)
else
ifeq ($(BSC_BUILD),DEBUG)
$(info ----- Debug build options -----)
BUILDFLAGS = $(GHCOPTDEBUGFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
TCLSTUB = $(TCLSTUBPROF)
TCLCLEAN = $(TCLCLEANPROF)
WISHSTUB = $(WISHSTUBPROF)
WISHCLEAN = $(WISHCLEANPROF)
else
ifeq ($(BSC_BUILD),NOOPT)
$(info ----- Unoptimized build options -----)
BUILDFLAGS = $(GHCFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
TCLSTUB =
TCLCLEAN =
WISHSTUB =
WISHCLEAN =
else
$(info ----- Normal build options -----)
BUILDFLAGS = $(GHCOPTFLAGS) $(GHCMAKEFLAGS) $(GHCRTSFLAGS)
EXTRAOBJ = $(EXTRAOBJNORMAL)
TCLSTUB =
TCLCLEAN =
WISHSTUB =
WISHCLEAN =
endif
endif
endif

# Choose a license policy
ifeq ($(BSC_LIC_POLICY),XGEN)
BUILDFLAGS += -DBSC_LIC_POLICY_XGEN
# To add the name of a specific customer to error messages,
# edit xgenCustomer in Authorization.hs
else
ifeq ($(BSC_LIC_POLICY),DATE_REVERT)
BSPEC_EXP_DAYS ?= 0
CUR_TIME_IN_SECS = $(shell date +%s)
EXP_TIME_IN_SECS ?= $(shell expr $(CUR_TIME_IN_SECS) + 60 \* 60 \* 24 \* $(BSPEC_EXP_DAYS))
BUILDFLAGS += -DBSC_LIC_POLICY_DATE_REVERT=$(EXP_TIME_IN_SECS)
else
ifneq ($(BSC_LIC_POLICY),DEFAULT)
ifneq ($(BSC_LIC_POLICY),)
$(error Unrecognized BSC_LIC_POLICY: $(BSC_LIC_POLICY))
endif
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
		$(BUILDFLAGS) $(BSCBUILDLIBS) $(EXTRAOBJ)
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
	$(RM) -f $(TCLCLEAN)
	$(BUILDCOMMAND) $(BUILDFLAGS) -c $(EXTRAOBJ)
	$(BUILDCOMMAND) $(BUILDFLAGS) $(BSCBUILDLIBS) \
		-o $@ \
		-no-hs-main $(WISHFLAGS) $(EXTRAOBJ) $(TCLSTUB) \
		-x c bluetcl_Main.hsc
	$(RM) -f $(TCLCLEAN)
	$(POSTBUILDCOMMAND)

BLUEWISHCP = cp -p bluetcl.hs bluewish.hs
BLUEWISHDIFF = diff -q bluetcl.hs bluewish.hs || $(BLUEWISHCP)

.PHONY: bluewish.hs
bluewish.hs: bluetcl.hs
	if test -f bluewish.hs; then $(BLUEWISHDIFF); else $(BLUEWISHCP); fi;

.PHONY: bluewish
bluewish: bluewish.hs bluewish_Main.hsc $(SOURCES) $(EXTRAOBJS)
	$(PREBUILDCOMMAND)
	$(RM) -f $(WISHCLEAN)
	$(BUILDCOMMAND) $(BUILDFLAGS) -c $(EXTRAOBJ)
	$(BUILDCOMMAND) $(BUILDFLAGS) $(BSCBUILDLIBS) \
		-o $@ \
		-no-hs-main $(WISHFLAGS) $(EXTRAOBJ) $(WISHSTUB) \
		-x c bluewish_Main.hsc
	$(RM) -f $(WISHCLEAN)
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
	$(FIND) . $(PARSEC_HS) $(STP_HS) $(YICES_HS) $(TCL_HS) \
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
