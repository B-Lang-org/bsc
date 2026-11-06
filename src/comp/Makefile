TOP:=$(shell pwd)/../..

# -----
# System tools

INSTALL ?= install
CABAL ?= cabal

RM = rm -f

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
# Intermediate files outside dist-newstyle (install-bluehs)
BUILDDIR?=$(TOP)/build

# Where package information is installed
LICDIR=$(PREFIX)/LICENSES

# -----
# GHC

GHC ?= ghc
# Parallelism for `cabal build -j`: on GHC >= 9.12 the project's semaphore
# shares the count with GHC's own module compilation, as `ghc --make -j`
# did; on older GHCs it bounds the packages built at once while each
# compiles serially (doc/cabal.md, Project settings and variants).
# Default the parallelism from the machine. Measured on a 228-module
# build (16-core/32-thread EPYC, GHC 9.14.1): wall time is 253.7s at
# -j1, 82.9s at -j4, 67.7s at -j12, and flat (within ~1%) from -j12
# through -j32 -- the module graph's average ready-set width (~5-6
# compiles) bounds useful parallelism well below the core count, and
# SMT threads add nothing. 16 captures the plateau with margin; each
# job also wants ~1 GB of headroom under -M (see GHCRTSFLAGS).
GHCJOBS ?= $(shell n=`nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 1`; if [ "$$n" -gt 16 ]; then echo 16; else echo "$$n"; fi)

# RTS options for the GHC that compiles the bsc package.
#
# A parallel compile runs up to GHCJOBS modules concurrently in ONE
# process sharing ONE heap, and -A gives each job its own allocation
# area inside it. A flat max-heap sized for one job therefore overflows
# intermittently as the number of jobs increases, depending on which
# large modules the scheduler happens to compile at the same time.
# Scale the cap with the job count: a 3 GB base plus 1 GB per job.
GHCMAXHEAP ?= $(shell expr 3 + $(GHCJOBS))G
# -A256m sits on the measured allocation-area plateau for parallel
# builds (repeated-measures sweep, idle machine: -A64m costs 5-8%,
# -A128m 1-3%, and -A256m/-A512m/-A1g are within noise of each other
# at the default -j). Total nursery is -A x jobs; at the default cap
# of 16 jobs that is 4 GB, well under -M.
GHCRTSFLAGS ?= +RTS -M$(GHCMAXHEAP) -A256m -RTS

# Build variant (PROF, DEBUG, or NOOPT) selects cabal.project.<variant>.
ifneq ($(BSC_BUILD),)
CABAL_PROJECT = cabal.project.$(shell echo $(BSC_BUILD) | tr A-Z a-z)
ifeq ($(wildcard $(TOP)/$(CABAL_PROJECT)),)
$(error BSC_BUILD=$(BSC_BUILD): no $(CABAL_PROJECT) (INSTALL.md))
endif
endif

CABAL_FLAGS = $(if $(CABAL_PROJECT),--project-file=$(CABAL_PROJECT)) --with-compiler=$(GHC) $(if $(strip $(GHCRTSFLAGS)),--ghc-options='$(GHCRTSFLAGS)')

# -----
# GHC package info

# If BSC_BUILD_PKGINFO is non-empty, generate LICENSES/LICENSE.ghc_pkgs.
ifeq ($(BSC_BUILD_PKGINFO),)
PKGINFO=
else
PKGINFO=$(LICDIR)/LICENSE.ghc_pkgs

# The ghc-pkg beside $(GHC), named like it (ghc-pkg-9.4.7 for ghc-9.4.7);
# set GHCPKG when the names differ.
GHCPKG ?= $(if $(findstring /,$(firstword $(GHC))),$(dir $(firstword $(GHC))))ghc-pkg$(patsubst ghc%,%,$(notdir $(firstword $(GHC))))

.PHONY: $(PKGINFO)
$(PKGINFO):
	mkdir -p -m 755 $(LICDIR)
	cd $(TOP) && GHCPKG="$(GHCPKG)" $(CABAL) exec -v0 $(CABAL_FLAGS) -- bash src/comp/make-ghc-pkg-info.sh --deps-of bsc > $(PKGINFO)
endif

# -----
# Build targets

BSCEXES = bsc
TCLEXES = bluetcl
UTILEXES = bsc2bsv bsv2bsc dumpbo dumpba vcdcheck
SHOWRULESEXES = showrules

EXES = $(BSCEXES) $(TCLEXES) $(UTILEXES) $(SHOWRULESEXES)

# Point the linker at the vendored solvers installed in $(PREFIX)/lib/SAT.
CABAL_ENV = LIBRARY_PATH="$(abspath $(PREFIX))/lib/SAT$${LIBRARY_PATH:+:$$LIBRARY_PATH}"

# Serialize this Make wrapper; Cabal parallelizes internally via -j$(GHCJOBS).
.NOTPARALLEL:

.PHONY: all
all: $(EXES)

.PHONY: version
version:
	./update-build-version.sh --module .

# Each executable is one cabal build, symlinked here so that src/comp/<exe>
# stays runnable in place.
.PHONY: $(EXES)
$(EXES): version
	cd $(TOP) && $(CABAL_ENV) $(CABAL) build -j$(GHCJOBS) $(CABAL_FLAGS) exe:$@
	ln -sf "$$(cd $(TOP) && $(CABAL) list-bin $(CABAL_FLAGS) bsc:exe:$@)" $@

# -----
# Install targets

.PHONY: install
install: $(BSCEXES) $(TCLEXES) install-bsc install-bluetcl

.PHONY: install-extra
install-extra: $(UTILEXES) $(SHOWRULESEXES) install-utils install-showrules

$(BINDIR)/%: %
	mkdir -p -m 755 $(BINDIR)
	$(INSTALL) -m 755 $(@F) $(BINDIR)/$(@F)

.PHONY: install-bsc
install-bsc: $(addprefix $(BINDIR)/,$(BSCEXES))
install-bsc: $(PKGINFO)

.PHONY: install-bluetcl
install-bluetcl: $(addprefix $(BINDIR)/,$(TCLEXES))
install-bluetcl: $(PKGINFO)

.PHONY: install-utils
install-utils: $(addprefix $(BINDIR)/,$(UTILEXES))
install-utils: $(PKGINFO)

.PHONY: install-showrules
install-showrules: $(addprefix $(BINDIR)/,$(SHOWRULESEXES))
install-showrules: $(PKGINFO)

# The bluehs runtime builds the library again, with this build's settings.
.PHONY: install-bluehs
install-bluehs:
	GHC='$(GHC)' CABAL='$(CABAL)' GHCJOBS='$(GHCJOBS)' GHCRTSFLAGS='$(GHCRTSFLAGS)' BSC_BUILD='$(BSC_BUILD)' \
		$(TOP)/util/bluehs/mk-dist.sh $(PREFIX)/bluehs $(BUILDDIR)/bluehs

# ----
# Other targets

tags:   *hs */*hs
	$(FIND) . ../Parsec ../vendor/stp/HaskellIfc ../vendor/yices/v2.6/HaskellIfc ../vendor/htcl \
		-type f -name \*hs | xargs hasktags
	mv tags tags.tmpfile
	sort tags.tmpfile > tags
	$(RM) tags.tmpfile

# -----
# Clean targets

.PHONY: clean
clean:
	$(RM) -rf $(EXES) $(TOP)/dist-newstyle $(TOP)/.ghc.environment.*

.PHONY: full_clean
full_clean: clean
	$(RM) -f BuildVersion.hs Warmup.hs
	$(RM) tags TAGS

# -----
