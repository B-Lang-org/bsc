PWD:=$(shell pwd)
PREFIX ?= $(PWD)/../../inst

INSTALL ?= install

IDIR = $(PREFIX)/enscript


INSTALL_FILES = \
	bsv.st \
	README \


.PHONY: all install clean realclean
all:

install:
	$(INSTALL) -m 755 -d $(IDIR)
	$(INSTALL) -m 644 $(INSTALL_FILES)  $(IDIR)	




clean:

realclean:
