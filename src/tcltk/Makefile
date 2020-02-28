CFLAGS += -Wall $(shell pkg-config --silence-errors --cflags-only-I tcl || echo -I/usr/include/tcl)

# We use GHC to compile this, so it has the proper RTS includes
%.o: %.c
	ghc $(CFLAGS) -c $<

libhtcl.a: haskell.o
	ar -r $@ $(filter %.o, $+)

.PHONY: install
install: libhtcl.a

.PHONY: clean full_clean
clean full_clean:
	rm -rf *.o *.a TAGS
