PWD := $(shell pwd)
TOP := $(PWD)

PREFIX   ?= $(TOP)/inst
BUILDDIR ?= $(TOP)/build

.PHONY: help
help:
	@echo 'This Makefile will create an installation of the Bluespec Compiler tools,'
	@echo 'in a directory named "inst".  This directory can be moved anywhere, but'
	@echo 'the contents should remain in the same relative locations.  Intermediate'
	@echo 'files are stored in a directory named "build".  The "clean" target will'
	@echo 'delete the "build" directory; the "full_clean" target will delete both'
	@echo 'the "build" and "inst" directories.'
	@echo
	@echo '    make  release      Build a release dir with the tools and docs'
	@echo
	@echo '    make  install-src  Build and install just the tools'
	@echo '    make  install-doc  Build and install just the documentation'
	@echo
	@echo '    make  check-smoke  Run a quick smoke test'
	@echo '    make  check-suite  Run the test suite (this will take time!)'
	@echo '    make  check-suite-parallel'
	@echo '                       Run the test suite in a way that can parallelize with -j'
	@echo
	@echo '    make  clean        Remove intermediate build-files unnecessary for execution'
	@echo '    make  full_clean   Restore to pristine state (pre-building anything)'

# -------------------------

.PHONY: rem_inst
rem_inst:
	rm -fr $(PREFIX)

.PHONY: rem_build
rem_build:
	rm -fr $(BUILDDIR)

# -------------------------

.PHONY: install-src
install-src:
	$(MAKE)  -C src  PREFIX=$(PREFIX)  install

.PHONY: install-doc
install-doc:
	$(MAKE)  -C doc  PREFIX=$(PREFIX)  install

.PHONY: install-release
install-release:
	$(MAKE)  -C release  PREFIX=$(PREFIX)  install

# -------------------------

.PHONY: release
release: install-src install-doc install-release

# -------------------------

# NOTE: We have to do things in a subshell and set PATH there, because the
# generated bluesim .exe is a shell script that expects 'bluetcl' to be located
# in $PATH. it's not enough to just set bsc...
.PHONY: check-smoke
check-smoke:
	@(export PATH=$(PREFIX)/bin:$(PATH); $(MAKE) -C examples/smoke_test smoke_test)

.PHONY: check-suite
check-suite:
	$(MAKE) -C testsuite

.PHONY: check-suite-parallel
check-suite-parallel:
	$(MAKE) -C testsuite checkparallel

# -------------------------

clean: rem_build
	-$(MAKE)  -C src      clean
	-$(MAKE)  -C doc      clean
	-$(MAKE)  -C release  clean

full_clean: rem_inst rem_build
	-$(MAKE)  -C src      full_clean
	-$(MAKE)  -C doc      full_clean
	-$(MAKE)  -C release  full_clean

# -------------------------
