TOP = ../../..
WANT_TCL=yes
include $(TOP)/platform.mk

# -----
# Tcl 8.5 requires a workaround

TCLVER=$(shell echo 'catch { puts [info tclversion]; exit 0}; exit 1' | $(TCLSH))
ifeq ($(TCLVER),8.5)
# Use -optc-D instead of -D, since not all versions of GHC pass -D to the C compiler
# (see GHC issue 24885)
GHCFLAGS += -optc-DTCL85
else
ifeq ($(TCLVER),8.6)
# No flags needed
else
$(error Unsupported Tcl version: $(TCLVER))
endif
endif

# -----

GHCFLAGS += -Wall ${TCL_INC_FLAGS}
GHC ?= ghc

# -----

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

# -----
