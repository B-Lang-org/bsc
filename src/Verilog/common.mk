# This file is shared among the various Verilog* directories.
# It assumes that the following variables are assigned:
#     VERI_FILES     = Verilog files to install (and test)
#     OTHER_FILES    = other files to install (and not test)
#     INSTALL_NAME   = directory name to use (Verilog, Verilog.Vivado, etc)
#     VCD_TEST_MODS  = any modules to test for VCD generation

# -------------------------

PWD:=$(shell pwd)
TOP:=$(PWD)/../..

INSTALL?=install -c
RM = rm -f

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/$(INSTALL_NAME)

.PHONY: all
all: test

# -------------------------
# Use various simulators to test that there are no basic errors

VCS ?= vcs
VCSCMD = $(VCS)  +v2k +libext+.v -y . +warn=all +define+TOP=Empty

IVERILOG = iverilog -tnull -Wall -y . -DTOP=Empty
CVC = cvc +libext+.v -y . +warn=all +define+TOP=Empty

PD = +define+$(1)
PDARGS = $(foreach a, $(1), $(call PD,$a))

MD = -D$(1)
MDARGS = $(foreach a, $(1), $(call MD,$a))

# -------------------------

# check that the files compile.
.PHONY: test_vcs
test_vcs:	$(VERI_FILES)
	$(VCSCMD) $+
	-$(RM) simv

# test whether the Verilog libs parse with various parametrizing macros defined
.PHONY: test
test:	$(VERI_FILES)
	$(IVERILOG)	$+
	$(IVERILOG) $(call MDARGS, BSV_NO_INITIAL_BLOCKS=1) $+
	$(IVERILOG) $(call MDARGS, BSV_ASSIGNMENT_DELAY='#0')  $+
	$(IVERILOG) $(call MDARGS, BSV_ASSIGNMENT_DELAY='#1')  $+
	$(IVERILOG) $(call MDARGS, BSV_POSITIVE_RESET) $+
	$(IVERILOG) $(call MDARGS, BSV_ASYNC_FIFO_RESET) $+
	$(IVERILOG) $(call MDARGS, BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(IVERILOG) $(call MDARGS, BSV_ASYNC_FIFO_RESET BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(IVERILOG) $(call MDARGS, BSV_POSITIVE_RESET BSV_ASYNC_FIFO_RESET BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(IVERILOG) $(call MDARGS, VIVADO) $+

.PHONY: testvcs
testvcs:	$(VERI_FILES)
	$(VCSCMD)  $+
	$(VCSCMD) $(call PDARGS, BSV_NO_INITIAL_BLOCKS=1)  $+
	$(VCSCMD) $(call PDARGS, BSV_ASSIGNMENT_DELAY='#0') $+
	$(VCSCMD) $(call PDARGS, BSV_ASSIGNMENT_DELAY='#1') $+
	$(VCSCMD) $(call PDARGS, BSV_POSITIVE_RESET) $+
	$(VCSCMD) $(call PDARGS, BSV_ASYNC_FIFO_RESET) $+
	$(VCSCMD) $(call PDARGS, BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(VCSCMD) $(call PDARGS, BSV_ASYNC_FIFO_RESET BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(VCSCMD) $(call PDARGS, BSV_POSITIVE_RESET BSV_ASYNC_FIFO_RESET BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	-$(RM) simv

.PHONY: testcvc
testcvc:	$(VERI_FILES)
	$(CVC) $+
	$(CVC) $(call PDARGS,  BSV_NO_INITIAL_BLOCKS=1) $+
	$(CVC) $(call PDARGS,  BSV_ASSIGNMENT_DELAY='#0') $+
	$(CVC) $(call PDARGS,  BSV_ASSIGNMENT_DELAY='#1') $+
	$(CVC) $(call PDARGS,  BSV_POSITIVE_RESET) $+
	$(CVC) $(call PDARGS,  BSV_ASYNC_FIFO_RESET) $+
	$(CVC) $(call PDARGS,  BSV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(CVC) $(call PDARGS,  BSV_ASYNC_FIFO_RESET SV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	$(CVC) $(call PDARGS,  BSV_POSITIVE_RESET BSV_ASYNC_FIFO_RESET SV_RESET_FIFO_HEAD BSV_RESET_FIFO_ARRAY) $+
	-$(RM) cvcsim verilog.log


.PHONY: test_race
test_race: $(VERI_FILES)
	$(VCSCMD) +race=all $+
	cat race.out.static

# -------------------------

.PHONY: install
install: install-veri-files
ifneq ($(OTHER_FILES),)
install: install-other-files
endif

$(INSTALLDIR):
	$(INSTALL) -m 755 -d $(INSTALLDIR)

.PHONY: install-veri-files
install-veri-files: $(VERI_FILES) $(INSTALLDIR)
	$(INSTALL) -m 644 $(VERI_FILES) $(INSTALLDIR)

.PHONY: install-other-files
install-other-files: $(OTHER_FILES) $(INSTALLDIR)
	$(INSTALL) -m 644 $(OTHER_FILES) $(INSTALLDIR)

.PHONY: clean
clean:
	-$(RM) *.dump a.out sim *.testout *.fsdb race.out.static simv
	-$(RM) -r csrc simv.daidir cvcsim verilog.log

.PHONY: full_clean
full_clean: clean
	# remove the copied modules, too
	$(RM) RegAligned.v ConfigRegN.v ConfigRegUN.v ConfigRegA.v BypassCrossingWire.v

# -------------------------

VCDGEN = $(addsuffix .testout,$(VCD_TEST_MODS))

VERILOG = $(CVC) +define+testBluespec
##VERILOG = iverilog -o simv -Wall -y . -DtestBluespec

.PHONY:	testout
testout:	$(VCDGEN)

.PHONY: %.testout
.KEEP:	%.testout
%.testout:	%.v
	$(RM) ./simv
	$(VERILOG) $<
	./cvcsim | tee $@

%.testdiff: %.testout
	diff $< $<.expected | tee $@

# -------------------------
