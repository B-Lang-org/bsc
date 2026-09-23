# include file to do make clean
# very gnu-make-specific
# version2

TEST_OSTYPE ?= $(shell $(CONFDIR)/../platform.sh ostype)
ifneq ($(TEST_OSTYPE), $(findstring $(TEST_OSTYPE), Linux Darwin))
  $(error TEST_OSTYPE environment not recognized: $(TEST_OSTYPE))
endif

TEST_MACHTYPE ?= $(shell $(CONFDIR)/../platform.sh machtype)
# TODO: Test for expected architectures?

MAKEFLAGS += --no-print-directory

# Make sure that the environments are consistent
LC_ALL = en_US.UTF-8
export LC_ALL

# Immediate subdirs with Makefiles, so we can recurse into them
SUBDIRS ?= $(dir $(wildcard */Makefile))

# For testing a release, setup a group of variables
TEST_RELEASE ?= $(CONFDIR)/../inst

# The following can also be defined (=0 or =1)
#
# VTEST = Whether to run Verilog backend tests (default =1)
# CTEST = Whether to run Bluesim backend tests (default =1)
# SYSTEMCTEST = Whether to run SystemC backend tests (default =1)
#         (Set this to 0 if libsystemc is not available)
# DO_INTERNAL_CHECKS = Whether to sanity check generated files (default =0)
#         (Set this to 0 if developer tools not installed)

TEST_BSDIR   ?= $(TEST_RELEASE)/lib
BLUESPECDIR = $(realpath $(TEST_BSDIR))
export BLUESPECDIR

TEST_BSC     ?= $(TEST_RELEASE)/bin/bsc
TEST_BLUETCL ?= $(TEST_RELEASE)/bin/bluetcl

# This tool will only be used if it exists
TEST_SHOWRULES ?= $(TEST_RELEASE)/bin/showrules

# These only need to exist when DO_INTERNAL_CHECKS=1
TEST_BSC2BSV  ?= $(TEST_RELEASE)/bin/bsc2bsv
TEST_DUMPBO   ?= $(TEST_RELEASE)/bin/dumpbo
TEST_DUMPBA   ?= $(TEST_RELEASE)/bin/dumpba
TEST_VCDCHECK ?= $(TEST_RELEASE)/bin/vcdcheck

TEST_CONFIG ?= $(CONFDIR)/config

TEST_BSC_VERILOG_SIM ?= iverilog

# The SystemC settings are derived with $(shell), and RUNTESTENV is expanded
# once per test file by parallel.mk, so a recursively expanded (?=) variable
# would re-run pkg-config and nm hundreds of times per test run.  Instead,
# assign with := behind an origin guard, which keeps the ?= override
# semantics, and export, so that a recursive child make sees origin
# "environment" and skips the derivation too.  The exported values are :=
# literals, copied into each recipe's environment without re-expansion; only
# an exported recursive variable re-runs its shell per recipe.
# When SYSTEMCTEST=0 the variables stay undefined and reach runtest as empty
# strings, which unix.exp never consults because SYSTEMCTEST=0 reaches it
# through make's command-line export.  An unset SYSTEMCTEST expands to empty,
# which is != 0, so the default path still derives.
ifneq ($(SYSTEMCTEST),0)

ifeq ($(origin TEST_SYSTEMC_INC),undefined)
TEST_SYSTEMC_INC := $(shell pkg-config --variable includedir systemc --silence-errors)
endif
export TEST_SYSTEMC_INC

ifeq ($(origin TEST_SYSTEMC_LIB),undefined)
TEST_SYSTEMC_LIB := $(shell pkg-config --variable libarchdir systemc --silence-errors)
endif
export TEST_SYSTEMC_LIB

# SystemC encodes the C++ standard it was built with into its
# sc_api_version_<ver>_cxx<std> symbol, and a translation unit compiled with a
# different standard references a differently-named symbol and fails to link
# (see sysc/kernel/sc_ver.h).  So read the standard off the installed library
# rather than assuming one -- SystemC 3.x needs at least C++17, which is newer
# than some compilers default to.  Empty when no library is found, which leaves
# pre-C++17 SystemC installations behaving as they did before.  The $(if)
# guard matters: with no library file a bare nm would read a.out.
ifeq ($(origin TEST_SYSTEMC_CXXFLAGS),undefined)
TEST_SYSTEMC_LIBFILE  := $(firstword $(wildcard \
	$(TEST_SYSTEMC_LIB)/libsystemc.dylib \
	$(TEST_SYSTEMC_LIB)/libsystemc.so \
	$(TEST_SYSTEMC_LIB)/libsystemc.a))
# -D reads the dynamic symbol table, which only an ELF shared object has.  A
# libsystemc.so installed stripped of its regular symbols exposes
# sc_api_version_ only there, while Mach-O keeps a single table and a static
# archive has no dynamic one, so .dylib and .a need plain nm.  Choosing on the
# file rather than on the host keeps a static-only installation working.
TEST_SYSTEMC_NMFLAGS  := $(if $(filter %.so,$(TEST_SYSTEMC_LIBFILE)),-D)
TEST_SYSTEMC_CXXFLAGS := $(if $(TEST_SYSTEMC_LIBFILE),$(shell nm $(TEST_SYSTEMC_NMFLAGS) $(TEST_SYSTEMC_LIBFILE) 2>/dev/null | \
	sed -E -n 's/.*sc_api_version_[0-9_]+_cxx20([0-9][0-9]).*/-std=c++\1/p' | head -1))
endif
export TEST_SYSTEMC_CXXFLAGS

endif

STATS_FILE ?= $(CONFDIR)/time.out

# The default test options should match what the user uses -- NOTHING
TEST_BSC_OPTIONS ?=

RUNTESTENV = MAKEFLAGS= BSCTEST=1 \
	BSC=$(TEST_BSC) BSC_OPTIONS="${TEST_BSC_OPTIONS}" BSDIR=$(TEST_BSDIR) \
	DUMPBO=$(TEST_DUMPBO) DUMPBA=$(TEST_DUMPBA) BSC2BSV=$(TEST_BSC2BSV) \
	VCDCHECK=$(TEST_VCDCHECK) SHOWRULES=$(TEST_SHOWRULES) \
	BLUESPECDIR=$(BLUESPECDIR) \
	BSC_VERILOG_SIM=$(TEST_BSC_VERILOG_SIM) \
	TEST_CONFIG_DIR=${TEST_CONFIG} \
	BLUETCL=$(TEST_BLUETCL) \
	OSTYPE=$(TEST_OSTYPE) \
	MACHTYPE=$(TEST_MACHTYPE) \
	LC_ALL=$(LC_ALL) \
	SYSTEMC_INC="$(TEST_SYSTEMC_INC)" \
	SYSTEMC_LIB="$(TEST_SYSTEMC_LIB)" \
	SYSTEMC_CXXFLAGS="$(TEST_SYSTEMC_CXXFLAGS)" \
	PATH="$(BLUESPECDIR)/../bin:$(PATH)"


## Track the overall time it took to run  runtest.  Make sure this command is the same as in unix.exp.
#TIME = /usr/bin/time -a -o $(STATS_FILE) -f "runtest, %S, %U, %e"
TIME =

## use RTFLAGS to pass runtest flag from the make file.
## E.g., make RTFLAGS = '-v -v ' foo.check     to get reasonable debug info.
RTFLAGS =
RUNTEST = $(TIME) runtest
## do not put --tool bsc here, since that will limit recursion into local directories
RUNTESTFLAGS ?= --tool ""
## for dejagnu 1.6.3+ to work in a subdirectory,
## we need to trigger the legacy way of finding the testsuitedir
RUNTESTFLAGS += --objdir .
## insert the user-specified flags at the end
RUNTESTFLAGS += --status $(RTFLAGS)

CHECKPREREQUISITES	?= clean localcheck


# run tests in current directory and recurse through subdirs
.PHONY: check
check:	$(CHECKPREREQUISITES)
	$(RUNTESTENV) $(RUNTEST) $(RUNTESTFLAGS)

.PHONY: fullparallel-setup
fullparallel-setup:
	time $(MAKE) clean
	time $(MAKE) enablelongtests

.PHONY: checkparallel-setup
checkparallel-setup:
	time $(MAKE) clean


## Allows override of local check command for top level makefile.
LOCALCHECKPREREQUISITES ?= localclean
LOCALCHKCMD ?= $(RUNTESTENV) $(RUNTEST) $(RUNTESTFLAGS) *.exp

# run tests in this directory only
.PHONY: localcheck
localcheck: $(LOCALCHECKPREREQUISITES)
	$(LOCALCHKCMD)

# This creates the file 'all_tests.mk', that is used by the 'run-tests'
# target in the 'parallel.mk' file.  It also checks for duplicates
# which can cause problems.
.PHONY: run-tests-setup
run-tests-setup:
	perl $(CONFDIR)/scripts/sort-by-time.pl $(tool) \
		| awk '{t=t " " $$0} END{print "ALL_TESTS :=" t}' \
		> $(CONFDIR)/all_tests.mk
	perl $(CONFDIR)/scripts/sort-by-time.pl $(tool) \
		| perl $(CONFDIR)/scripts/double-directory.pl


INIT ?= FORCE_INITIALIZE=$(tool)
PARALLEL_FLAGS ?= $(INIT) LOCAL_TIME_WALK=1


#the reason this is a rule rather than a separate script is so we do not need to hunt down
#CONFDIR again inside the script.
.PHONY: generate-stats
generate-stats:
	@echo ""
	@echo "                ===  CUMULATIVE SUMMARY ==="
	@find . -name time.out -exec cat '{}' \; | perl $(CONFDIR)/scripts/collapse.pl
	@echo ""
	@echo "=== Top 100 longest testcases ==="
	@find . -name time.out -exec cat '{}' \; | perl $(CONFDIR)/scripts/times-by-directory.pl  | head -100
	@echo ""
	@echo "=== Brief list of results ==="
	@find . -name '*.sum' | sort | perl $(CONFDIR)/scripts/process-summary-file.pl


#we call "false" in the else branch to cause a error exit status

# NB: run-tests-setup must run AFTER the *-setup target completes, not as a
# sibling prerequisite: under a parallel make (-j) sibling prerequisites run
# concurrently, so the test list (generated by run-tests-setup with
# "find . -name '*.exp'") races against fullparallel-setup's
# "make enablelongtests", which is what creates the .exp files in
# bsc.long_tests.  Losing that race silently drops the long tests from the
# run.  Invoking run-tests-setup from the recipe serializes it.

#example usage: make -j9 INIT=bsc checkparallel
.PHONY: checkparallel
checkparallel: checkparallel-setup
	$(MAKE) run-tests-setup
	if $(MAKE) -f $(CONFDIR)/parallel.mk CONFDIR=$(CONFDIR) -k INIT=FORCE_INITIALIZE=$(INIT) run-tests ; \
	then $(MAKE) generate-stats ;\
	else $(MAKE) generate-stats ; false ;\
	fi

.PHONY: fullparallel
fullparallel: fullparallel-setup
	$(MAKE) run-tests-setup
	if $(MAKE) -f $(CONFDIR)/parallel.mk CONFDIR=$(CONFDIR) -k tool=bsc run-tests ; \
	then $(MAKE) generate-stats ;\
	else $(MAKE) generate-stats ; false ;\
	fi
