# for "make clean" to work everywhere

CONFDIR := $(shell git rev-parse --show-toplevel)

include $(CONFDIR)/clean.mk
