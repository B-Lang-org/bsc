PWD := $(shell pwd)
TOP := $(PWD)

PREFIX   ?= $(TOP)/inst
BUILDDIR ?= $(TOP)/build

.PHONY: all
all: install

# -------------------------

.PHONY: rem_inst
rem_inst:
	rm -fr $(PREFIX)

.PHONY: rem_build
rem_build:
	rm -fr $(BUILDDIR)

# -------------------------

.PHONY: install
install:
	$(MAKE)  -C src  PREFIX=$(PREFIX)  install

.PHONY: install-doc
install-doc:
	$(MAKE)  -C doc  PREFIX=$(PREFIX)  install

# In the future, this will be much more expansive, and run the actual test
# suite once it's open sourced.
#
# NOTE: We have to do things in a subshell and set PATH there, because the
# generated bluesim .exe is a shell script that expects 'bluetcl' to be located
# in $PATH. it's not enough to just set bsc...
.PHONY: check
check:
	@(export PATH=$(PREFIX)/bin:$(PATH); $(MAKE) -C examples/smoke_test smoke_test)

# -------------------------

clean: rem_inst rem_build
	-$(MAKE)  -C src  clean
	-$(MAKE)  -C doc  clean

full_clean: rem_inst rem_build
	-$(MAKE)  -C src  full_clean
	-$(MAKE)  -C doc  full_clean

# -------------------------
