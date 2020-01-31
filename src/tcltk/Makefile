## Bluespec Makefile for building tcl

PWD := $(shell pwd)
TOP := $(PWD)/../..
include $(TOP)/platform.mk

DIRLIST = tcltk8.5.4 itcl3.4 itk3.4 HaskellTcl

LIBFILES = libtclstub8.5.a libtkstub8.5.a libtcl8.5.a libtk8.5.a

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

itcl3.4 itk3.4 HaskellTcl: | tcltk8.5.4
itk3.4: | itcl3.4
HaskellTcl: | itcl3.4 itk3.4
