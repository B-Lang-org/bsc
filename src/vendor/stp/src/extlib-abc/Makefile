SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard aig/*/*.c)
OBJS = $(SRCS:.c=.o)
CFLAGS += -I.


libabc.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) $(OBJS) *~ *.a .#* depend

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
