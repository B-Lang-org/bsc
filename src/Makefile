PWD := $(shell pwd)
TOP := $(PWD)/..

PREFIX?=$(TOP)/inst

.PHONY: all
all: install

.PHONY: install clean full_clean
install clean full_clean:
	$(MAKE)  -C stp        PREFIX=$(PREFIX)  $@
	$(MAKE)  -C yices      PREFIX=$(PREFIX)  $@
	$(MAKE)  -C tcltk      PREFIX=$(PREFIX)  $@
	# we need to build targets from here sequentially, as they operate in the same workspace
	$(MAKE)  -C comp -j1   PREFIX=$(PREFIX)  $@
	$(MAKE)  -C Libraries  PREFIX=$(PREFIX)  $@
	$(MAKE)  -C exec       PREFIX=$(PREFIX)  $@
	$(MAKE)  -C VPI        PREFIX=$(PREFIX)  $@
	$(MAKE)  -C Verilog    PREFIX=$(PREFIX)  $@
	$(MAKE)  -C Verilog.Quartus  PREFIX=$(PREFIX)  $@
	$(MAKE)  -C Verilog.Vivado   PREFIX=$(PREFIX)  $@
	$(MAKE)  -C bluetcl    PREFIX=$(PREFIX)  $@
	$(MAKE)  -C sim        PREFIX=$(PREFIX)  $@

