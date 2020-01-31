SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = main.cpp Globals.cpp
OBJS = $(SRCS:.cpp=.o)


# Build as a library; final linking to an executable will be done by the
# topmost Makefile.
libmain.a: $(filter-out main.o,$(OBJS)) | main.o
	$(RM) $@
	$(AR) qcs $@ $^

.PHONY: clean
clean:
	$(RM) *.o *~ *.a .#* depend

FORCE:

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
