AR	= ar -r

CCFLAGS += -Wall $(shell pkg-config --cflags-only-I tcl)

ifdef DEBUG
#### for debug
#EXTRAFLAGS   += -debug -optc -g -opta -g -keep-tmp-files
EXTRAFLAGS   += -debug -opta -g -keep-tmp-files
CCFLAGS += -g
else
EXTRAFLAGS += -fasm
endif

GHC ?= ghc
GHCFLAGS += -Wall -fno-warn-unused-binds -fno-warn-unused-matches -H128m $(EXTRAFLAGS)
GHCCCFLAGS += $(CCFLAGS) $(EXTRAFLAGS)


.PHONY: all
all: install

libhtcl.a: htclFunctions.o haskellCall.o
	$(AR)  $@  $(filter %.o, $+)


haskellCall.o: haskellCall.hsc

%.o: %.c
	$(CC) $(CCFLAGS) -c $<

# Use GHC to compile C files which use Haskell includes etc.
%.o: %.hsc
	$(GHC)  $(GHCCCFLAGS) -c -x c  $<

.PHONY: install
install: libhtcl.a

.PHONY: TAGS
TAGS: *.c *.h
	etags $+

.PHONY: clean full_clean
clean full_clean:
	rm -rf *.o *.a TAGS
