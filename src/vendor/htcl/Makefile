GHCFLAGS += -Wall $(shell pkg-config --silence-errors --cflags-only-I tcl || echo -I/usr/include/tcl)

ifeq ($(USING_STACK),yes)
GHC ?= stack ghc --
else
GHC ?= ghc
endif

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
