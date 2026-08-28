PWD:=$(shell pwd)
TOP:=$(PWD)/../..

# Common defines use by Makefiles here and in subdirectories
# Requires that TOP be set
include common.mk

DIRS = \
	Base1 \
	Base2 \
	Base3-Contexts \
	Base3-Math \
	Base3-Misc \

# Build order for the libraries
BUILD_ORDER= \
	Base1 \
	Base2 \
	Base3-Misc \
	Base3-Contexts \
	Base3-Math \

# Find files to build tags
SRCS = $(shell find . -name "*.bsv")

.PHONY: all install clean full_clean

all: install TAGS

build:
	$(foreach dir, $(BUILD_ORDER), $(MAKE) -C $(dir) $@ &&) true

install: build
	install -d $(INSTALLDIR)
	install -m644 $(BUILDDIR)/* $(INSTALLDIR)
	for dir in $(DIRS); do \
	  install -d $(SRCSINSTALLDIR)/$$dir; \
	  files=$$(ls $$dir/*.bs $$dir/*.bsv 2>/dev/null); \
	  [ -n "$$files" ] && install -m644 $$files $(SRCSINSTALLDIR)/$$dir || true; \
	done

TAGS: $(SRCS)
	$(TOP)/util/scripts/btags $+

clean full_clean:
	$(foreach dir, $(DIRS), $(MAKE) -C $(dir) $@;)
	@rm -f *~ TAGS

