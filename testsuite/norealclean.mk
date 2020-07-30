
# include file for standard make targets
# does not include realclean target
# because some important Makefiles define that locally
# very gnu-make-specific

include $(CONFDIR)/suitemake.mk
include $(CONFDIR)/cleanonly.mk
