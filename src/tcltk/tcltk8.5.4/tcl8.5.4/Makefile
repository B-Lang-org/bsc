## Bluespec Makefile for building tcl
## and installing 

PWD:=$(shell pwd)
TOP:=$(PWD)/../../../..

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/tcllib/tcl8.5

DIRLIST = unix library

.PHONY: all
all: install

.PHONY: install
install: 
	make -C unix -f Makefile.bluespec
	make -C library LIBDIR=$(INSTALLDIR) -f Makefile.bluespec $@

.PHONY: clean
clean :
	$(foreach dir, $(DIRLIST), \
		$(MAKE) -C $(dir) -f Makefile.bluespec $@ ; )

.PHONY: full_clean
full_clean: clean
