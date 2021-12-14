PWD:=$(shell pwd)
TOP:=$(PWD)/../..

INSTALL?= install

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/Verilator

.PHONY: install
install:
	$(INSTALL) -m 755 -d $(INSTALLDIR)/
	$(INSTALL) -m 755 sim_main.cpp $(INSTALLDIR)/sim_main.cpp
	$(INSTALL) -m 755 verilator_config.vlt $(INSTALLDIR)/verilator_config.vlt

.PHONY: clean full_clean
clean full_clean:

