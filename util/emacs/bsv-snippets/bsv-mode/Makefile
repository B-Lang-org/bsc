PWD:=$(shell pwd)
PREFIX?=$(PWD)/../../../../inst/util
THISDIR=$(PREFIX)/emacs/bsv-snippets/bsv-mode
INSTALL?=install -c

INSTALL_FILES = *

.PHONY:	all
all:


.PHONY:	release
install: 
	$(INSTALL) -m 755 -d $(THISDIR)
	$(INSTALL) -m 644 $(INSTALL_FILES) $(THISDIR) 
