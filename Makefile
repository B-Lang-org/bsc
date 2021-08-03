PWD := $(shell pwd)
TOP := $(PWD)

PREFIX   ?= $(TOP)/inst
BUILDDIR ?= $(TOP)/build

INSTALL?=install -c

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

REL_LICENSES = \
	LICENSE.ghc \
	LICENSE.hbc \
	LICENSE.parsec \
	LICENSE.stp \
	LICENSE.stp_components \
	LICENSE.yices \
	LICENSE.yices-painless \

.PHONY: install-README
install-README:
	$(INSTALL) -m 755 -d $(PREFIX)
	$(INSTALL) -m 644  release/tarball-README  $(PREFIX)/README
	$(INSTALL) -m 644  release/tarball-COPYING $(PREFIX)/COPYING
	$(INSTALL) -m 755 -d $(PREFIX)/LICENSES
	$(INSTALL) -m 644  $(addprefix LICENSES/,$(REL_LICENSES))  $(PREFIX)/LICENSES/

# -------------------------

.PHONY: release
release: install-src install-doc install-README

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

# -------------------------

clean: rem_build
	-$(MAKE)  -C src  clean
	-$(MAKE)  -C doc  clean

full_clean: rem_inst rem_build
	-$(MAKE)  -C src  full_clean
	-$(MAKE)  -C doc  full_clean

# -------------------------
