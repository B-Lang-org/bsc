
# include file to do make clean
# very gnu-make-specific
# version 3

.PHONY:	dummy

dummy:
	echo 'make with no args - ???'
# include base targets (from norealclean)
# add in the realclean target (used by most Makefiles)
include $(CONFDIR)/norealclean.mk
include $(CONFDIR)/realclean.mk
