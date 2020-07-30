# for "make clean" to work everywhere

CONFDIR = $(realpath ../..)

# Don't include the subdir with strange characters,
# because otherwise the top-level makefiles will break
SUBDIRS = 

include $(CONFDIR)/clean.mk

DONTKEEPFILES += dir?with?many?spec?ial?char?acters

