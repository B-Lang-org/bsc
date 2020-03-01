SRCTOP = ..
include $(SRCTOP)/Makefile.common

# Workaround for flex < 2.5.20 which do not support the -f flag nor provide *_destroy functions
OLD_FLEX=$(shell flex --version | awk -F '[ .]' '{ print ($$(NF-2) < 2 || $$(NF-2) == 2 && ($$(NF-1) < 5 || $$(NF-1) == 5 && $$NF < 20)) }')

ifeq (1,$(OLD_FLEX))
LEX=flex -Ce
else
#`From the flex manual>: -Cfe' is often a good compromise between speed and size for production scanners.
LEX=flex -Cfe
endif

YACC=bison --debug -v

SRCS = $(foreach foo,cvc smt smt2,lex$(foo).cpp parse$(foo).cpp) LetMgr.cpp
OBJS = $(SRCS:.cpp=.o)


libparser.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

lex%.cpp: %.lex parse%.hpp ../AST/AST.h
	$(LEX) -o$@ -P$* $<
ifeq (1,$(OLD_FLEX))
	echo "int $*lex_destroy(void) { return 0; }" >> $@
endif

parse%.cpp parse%.hpp: %.y
	$(YACC) -o parse$*.cpp -d -p $* $<


clean:
	$(RM) *.o *~ *.a .#* depend lex*.cpp parse*.cpp parse*.hpp *.output

ifeq (,$(filter clean configclean distclean,$(MAKECMDGOALS)))
depend: $(SRCS)
	@$(call makedepend,$@,$(SRCS))

-include depend
endif
