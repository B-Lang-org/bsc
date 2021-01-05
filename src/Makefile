PWD := $(shell pwd)
TOP := $(PWD)/..

include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst
LIBDIR?=$(PREFIX)/lib

ifndef NO_DEPS_CHECKS
CC_TOOLS=$(CC) $(CXX) $(LD)
BSC_TOOLS=ghc ghc-pkg
BLUETCL_TOOLS=tclsh
YICES_TOOLS=gperf autoconf
STP_TOOLS=flex bison

TOOLS=$(CC_TOOLS) \
      $(BSC_TOOLS) \
      $(BLUETCL_TOOLS) \
      $(YICES_TOOLS) \
      $(STP_TOOLS) \

GHC_PKGS=regex-compat syb old-time split

SUBMODS=vendor/yices/v2.6/yices2

# Check all the necessary build tools are present
pathsearch=$(firstword $(wildcard $(addsuffix /$(1),$(subst :, ,$(PATH)))))
checktool=$(if $(call pathsearch,$(1)),,$(error Tool $(1) could not be found))
$(foreach tool,$(TOOLS),$(call checktool,$(tool)))

# Check Haskell package dependencies
checkghcpkg=$(if $(shell ghc-pkg list --simple-output $(1)),,$(error GHC package $(1) not installed))
$(foreach pkg,$(GHC_PKGS),$(call checkghcpkg,$(pkg)))

# Check all submodules are initialized
define SUBMOD_MSG
Submodule $(1) missing. Initialize with
    git submodule update --init --recursive
endef
checksubmod=$(if $(wildcard $(1)/.git),,$(error $(SUBMOD_MSG)))
$(foreach submod,$(SUBMODS),$(call checksubmod,$(submod)))
endif # NO_DEPS_CHECKS

.PHONY: all
all: install

.PHONY: install clean full_clean
install clean full_clean:
	$(MAKE)  -C vendor/stp   PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C vendor/yices PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C vendor/htcl  PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	# we need to build targets from here sequentially, as they operate in the same workspace
	$(MAKE)  -C comp -j1   PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C Libraries  PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C exec       PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C VPI        PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C Verilog    PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C Verilog.Quartus  PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C Verilog.Vivado   PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C bluetcl    PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@
	$(MAKE)  -C bluesim    PREFIX=$(PREFIX)  LIBDIR=$(LIBDIR)  $@

