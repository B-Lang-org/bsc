## Bluespec Makefile for building tcl

PWD := $(shell pwd)
TOP := $(PWD)/../..
include $(TOP)/platform.mk

DIRLIST = HaskellTcl

.PHONY: all install
all install: $(DIRLIST)

.PHONY: $(DIRLIST)
$(DIRLIST):
	$(MAKE) -C $@ -f Makefile.bluespec install

.PHONY: clean full_clean
clean full_clean:
	$(foreach dir, $(DIRLIST), \
		$(MAKE) -C $(dir) -f Makefile.bluespec $@ ; )
	rm -rf inst
