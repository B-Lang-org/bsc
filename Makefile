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

.PHONY: rem_stack
rem_stack:
	rm -f stack.yaml stack.yaml.lock
	rm -fr $(TOP)/.stack-work
	rm -fr $(TOP)/src/.stack-work 

# -------------------------

.PHONY: install
install:
	$(MAKE)  -C src  PREFIX=$(PREFIX)  install

# -------------------------

.PHONY: stack-install
stack-install:
	stack init --force
	stack install regex-compat syb old-time split
	-$(MAKE)  -C src  PREFIX=$(PREFIX) NO_DEPS_CHECKS=yes USING_STACK=yes install

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

full_clean: rem_inst rem_build rem_stack
	-$(MAKE)  -C src  full_clean

