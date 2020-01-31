PWD:=$(shell pwd)
PREFIX?=$(PWD)/../../inst/util
THISDIR=$(PREFIX)/emacs
INSTALL?=install -c

INSTALL_FILES = bsv-mode/bsv-mode.el bsv-mode/bsv-mode-22.el  bsv-mode/bsv-mode-23.el mark.el emacs20-extras.el README bsvtags
INSTALL_EXE   = bsvtags

.PHONY:	all
all:
	cd bsv-snippets && make

.PHONY:	release
install: 
	$(INSTALL) -m 755 -d $(THISDIR)
	$(INSTALL) -m 644 $(INSTALL_FILES) $(THISDIR) 
	$(INSTALL) -m 755 $(INSTALL_EXE)   $(THISDIR) 
	cd bsv-snippets     && make install
