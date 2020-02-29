SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard *.cpp)
OBJS = $(SRCS:.cpp=.o)


libabstractionrefinement.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

clean:
	$(RM) *.o *~ *.a .#* depend

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
