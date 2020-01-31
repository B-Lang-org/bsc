PWD:=$(shell pwd)
PREFIX?=$(PWD)/../../../inst/util
THISDIR=$(PREFIX)/emacs/bsv-snippets
INSTALL?=install -c

INSTALL_FILES = BsvSnippetSummary.txt README.txt *.el .emacs

.PHONY:	all
all:
	perl makedoc.pl > BsvSnippetSummary.txt

.PHONY:	release
install: 
	$(INSTALL) -m 755 -d $(THISDIR)
	$(INSTALL) -m 644 $(INSTALL_FILES) $(THISDIR) 
	cd bsv-mode && make install



