# for "make clean" to work everywhere

CONFDIR = $(realpath ../..)

include $(CONFDIR)/clean.mk

# Don't delete the Verilog file
KEEPFILES = Verilog_SRAM_model.v

# Makefile.release might create this, so delete it
DONTKEEPFILES = install
