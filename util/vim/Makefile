PWD:=$(shell pwd)
PREFIX ?= $(PWD)/../../inst

INSTALL ?= install

IDIR = $(PREFIX)/vim

.PHONY: all install release clean realclean
all:

install:
	$(INSTALL) -m 755 -d $(IDIR)
	$(INSTALL) -m 755 -d $(IDIR)/ftdetect
	$(INSTALL) -m 755 -d $(IDIR)/syntax
	$(INSTALL) -m 755 -d $(IDIR)/indent
	$(INSTALL) -m 644 README $(IDIR)
	$(INSTALL) -m 644 ftdetect/bsv.vim $(IDIR)/ftdetect
	$(INSTALL) -m 644 syntax/bsv.vim $(IDIR)/syntax
	$(INSTALL) -m 644 indent/bsv.vim $(IDIR)/indent




clean:

realclean:
