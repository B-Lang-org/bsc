# include file to do make clean
# very gnu-make-specific
# version2

TEST_OSTYPE ?= $(shell $(CONFDIR)/ostype.sh)
ifneq ($(TEST_OSTYPE), $(findstring $(TEST_OSTYPE), Linux Darwin))
  $(error TEST_OSTYPE environment not recognized: $(TEST_OSTYPE))
endif

MAKEFLAGS += --no-print-directory

# Make sure that the environments are consistent
LC_ALL = C
export LC_ALL

# Immediate subdirs with Makefiles, so we can recurse into them
SUBDIRS ?= $(dir $(wildcard */Makefile))

# For testing a release, setup a group of variables
TEST_RELEASE ?= $(CONFDIR)/../bsc/inst

# This enables tests that use bsc-contrib libraries
# (the value should be an "inst" directory)
ifneq ($(wildcard $(TEST_RELEASE)/../../bsc-contrib/inst/),)
TEST_CONTRIB ?= $(TEST_RELEASE)/../../bsc-contrib/inst
else
ifneq ($(wildcard $(CONFDIR)/../bsc-contrib/inst/),)
TEST_CONTRIB ?= $(CONFDIR)/../bsc-contrib/inst
endif
endif

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
TEST_VCDCHECK ?= $(TEST_RELEASE)/bin/vcdcheck

TEST_CONFIG ?= $(CONFDIR)/config

TEST_BSC_VERILOG_SIM ?= iverilog

TEST_SYSTEMC_INC ?= $(pkg-config --variable includedir systemc --silence-errors)
TEST_SYSTEMC_LIB ?= $(pkg-config --variable libarchdir systemc --silence-errors)

STATS_FILE ?= $(CONFDIR)/time.out

# The default test options should match what the user uses -- NOTHING
TEST_BSC_OPTIONS ?=

RUNTESTENV = MAKEFLAGS= BSCTEST=1 \
	CONTRIB_INST=$(TEST_CONTRIB) \
	BSC=$(TEST_BSC) BSC_OPTIONS="${TEST_BSC_OPTIONS}" BSDIR=$(TEST_BSDIR) \
	DUMPBO=$(TEST_DUMPBO) BSC2BSV=$(TEST_BSC2BSV) \
	VCDCHECK=$(TEST_VCDCHECK) SHOWRULES=$(TEST_SHOWRULES) \
	BLUESPECDIR=$(BLUESPECDIR) \
	BSC_VERILOG_SIM=$(TEST_BSC_VERILOG_SIM) \
	TEST_CONFIG_DIR=${TEST_CONFIG} \
	BLUETCL=$(TEST_BLUETCL) \
	OSTYPE=$(TEST_OSTYPE) LC_ALL=$(LC_ALL) \
	SYSTEMC_INC=$(TEST_SYSTEMC_INC) \
	SYSTEMC_LIB=$(TEST_SYSTEMC_LIB) \
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
RUNTESTFLAGS += --status $(RTFLAGS)

# standard targets
.PHONY:	check localcheck


CHECKPREREQUISITES	?= clean localcheck


# run tests in current directory and recurse through subdirs
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
localcheck: $(LOCALCHECKPREREQUISITES)
	$(LOCALCHKCMD)

# Force all_tests.mk to be built exactly once at the top level invocation of make
# rather than running perl/find once per test subdir. This means the list is always
# up to date if we add new tests, but also isn't re-calculated unnecessarily.
ifeq (0,${MAKELEVEL})
DUMMY := $(shell perl $(CONFDIR)/scripts/sort-by-time.pl $(tool) | awk '{t=t " " $$0} END{print "ALL_TESTS :=" t}' > $(CONFDIR)/all_tests.mk)
endif

include $(CONFDIR)/all_tests.mk

.PHONY: double-directory-check
double-directory-check:
	perl $(CONFDIR)/scripts/sort-by-time.pl $(tool) | perl $(CONFDIR)/scripts/double-directory.pl

INIT ?= FORCE_INITIALIZE=$(tool)
PARALLEL_FLAGS ?= $(INIT) LOCAL_TIME_WALK=1


.PHONY: $(ALL_TESTS)
$(ALL_TESTS):
	cd $(dir $@) && $(RUNTESTENV) $(RUNTEST) $(RUNTESTFLAGS) $(PARALLEL_FLAGS) $(notdir $@)


.PHONY: run-tests
run-tests: double-directory-check $(ALL_TESTS)

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

#example usage: make -j9 INIT=bsc checkparallel
.PHONY: checkparallel
checkparallel: checkparallel-setup
	if $(MAKE) -k INIT=FORCE_INITIALIZE=$(INIT) run-tests ; \
	then $(MAKE) generate-stats ;\
	else $(MAKE) generate-stats ; false ;\
	fi

.PHONY: fullparallel
fullparallel: fullparallel-setup
	if $(MAKE) -k tool=bsc run-tests ; \
	then $(MAKE) generate-stats ;\
	else $(MAKE) generate-stats ; false ;\
	fi
