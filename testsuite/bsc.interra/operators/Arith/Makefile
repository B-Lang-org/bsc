.PHONY:	clean all

all:
	for i in ${SUBDIRS} ; do \
	  if [ -d $$i ] ; then \
	    cd $$i ; ${MAKE} || exit 1 ; cd .. ; fi ; done

PWD=$(shell pwd)
CONFDIR = $(realpath ../../..)
DONTKEEPFILES = Vectors.bsv

include $(CONFDIR)/clean.mk
