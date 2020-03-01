SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard  *.cpp)
OBJS = $(SRCS:.cpp=.o)


#Make the ast library for use by other modules
libprinter.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) *.o *~ *.a .#* depend

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend

