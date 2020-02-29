SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard *.cpp)
SRCS += $(wildcard AIG/*.cpp)
SRCS += $(wildcard ASTNode/*.cpp)
OBJS = $(SRCS:.cpp=.o)

libtosat.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) *.o */*.o *~ *.a .#* depend

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
