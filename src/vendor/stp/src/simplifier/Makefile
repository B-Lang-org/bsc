SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard *.cpp)
SRCS += $(wildcard constantBitP/*.cpp)
OBJS = $(SRCS:.cpp=.o)


libsimplifier.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) *.o */*.o *~ *.a .#* depend

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
