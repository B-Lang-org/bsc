SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard  *.cpp)
SRCS += $(wildcard  NodeFactory/*.cpp)
OBJS = $(SRCS:.cpp=.o)
OBJS += ASTKind.o


#Make the ast library for use by other modules
libast.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

# ASTKind.h and ASTKind.cpp are automatically generated
ASTKind.h ASTKind.cpp: ASTKind.kinds genkinds.pl
	./genkinds.pl

.PHONY: clean
clean:
	$(RM) *.o */*.o *~ *.a  .#* depend ASTKind.cpp ASTKind.h

depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend

