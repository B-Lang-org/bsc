SRCTOP = ..
include $(SRCTOP)/Makefile.common

SRCS = $(wildcard *.cpp)
OBJS = $(SRCS:.cpp=.o)
LIB = libminisat.a

# exported variables override those set in recursive makefiles.
export COPTIMIZE=$(CFLAGS_M32) $(CFLAGS_FPIC) -O3 


.PHONY:core
core: $(LIB)

# $(LIB) depends on */lib$(SUB)_release.a and will be rebuilt only if they have been updated
$(LIB): core/libcore_release.a core_prop/libcore_prop_release.a simp/libsimp_release.a utils/libutils_release.a cryptominisat2/libminisat.a $(OBJS)
	$(RM) $@
	$(call arcat,$@,$(filter %.a,$^))
	$(AR) qcs $@ $(filter %.o,$^)

core_prop/libcore_prop_release.a: FORCE
	$(MAKE) LIB="core_prop" -C core_prop libr
core/libcore_release.a: FORCE
	$(MAKE) LIB="core" -C core libr
simp/libsimp_release.a: FORCE
	$(MAKE) LIB="simp" -C simp libr
utils/libutils_release.a: FORCE
	$(MAKE) LIB="utils" -C utils libr
cryptominisat2/libminisat.a: FORCE
	$(MAKE) -C cryptominisat2 lib all
FORCE:

.PHONY: clean
clean:
	$(RM) *.o *~ *.a .#*
	$(MAKE) -C core    clean
	$(MAKE) -C core_prop    clean
	$(MAKE) -C simp    clean
	$(MAKE) -C utils   clean
	$(MAKE) -C cryptominisat2 clean

CryptoMinisat.o: CFLAGS += -Icryptominisat2/mtl -Imtl -I$(SRCTOP)
