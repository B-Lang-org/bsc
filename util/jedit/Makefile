PWD:=$(shell pwd)
PREFIX ?= $(PWD)/../../inst

INSTALL ?= install

IDIR = $(PREFIX)/jedit


INSTALL_FILES = \
	bsv.xml \
	README \


.PHONY: all install clean realclean
all:

install:
	$(INSTALL) -m 755 -d $(IDIR)
	$(INSTALL) -m 644 $(INSTALL_FILES)  $(IDIR)	

clean:

realclean:
