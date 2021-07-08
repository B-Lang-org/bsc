TOP = ../../..
WANT_TCL=yes
include $(TOP)/platform.mk

GHCFLAGS += -Wall ${TCL_INC_FLAGS}
GHC ?= ghc

# We use GHC to compile this, so it has the proper RTS includes
%.o: %.c
	$(GHC) $(GHCFLAGS) -c $<

libhtcl.a: haskell.o
	$(AR) -r $@ $(filter %.o, $+)

.PHONY: install
install: libhtcl.a

.PHONY: clean full_clean
clean full_clean:
	$(RM) -rf *.o *.a TAGS
