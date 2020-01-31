PWD:=$(shell pwd)
PREFIX ?= $(PWD)/../../inst/util

INSTALL ?= install

IDIR = $(PREFIX)/bsim_standalone

.PHONY: all install release clean realclean
all:

install:
	$(INSTALL) -m 755 -d $(IDIR)
	$(INSTALL) -m 644 Makefile.bsim_standalone $(IDIR)
	$(INSTALL) -m 644 main.cxx.template $(IDIR)

release: install

clean:

realclean:
