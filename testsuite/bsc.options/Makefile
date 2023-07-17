# for "make clean" to work everywhere

CONFDIR = $(realpath ..)

DONTKEEPFILES = *.post-m4 *.post-m4-stage1 \
		simfiles bfiles vfiles incfiles srcfiles vfiles_link \
		SplitIfNested.bs.expandif.atsexpand.expected \
		NoSplitIfNested.bs.expandif.atsexpand.expected \
		NoSplitIfNested.bs.noexpandif.atsexpand.expected \
		foo bar baz

include $(CONFDIR)/clean.mk
