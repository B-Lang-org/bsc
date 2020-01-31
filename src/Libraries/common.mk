#  Requires that TOP be set

PREFIX?=$(TOP)/inst
LIBDIR=$(abspath $(PREFIX)/lib)
BINDIR=$(abspath $(PREFIX)/bin)

# Where files are ultimately installed
INSTALLDIR=$(LIBDIR)/Libraries

# Where files are built
# (separate from the install location, to avoid recompiling)
BUILDDIR=$(abspath $(TOP)/build/bsvlib)

# Mark the libraries as standard (for bluetcl queries, etc)
BSCFLAGS_EXT = -stdlib-names
# Put the generated object files in BUILDDIR
BSCFLAGS_EXT += -bdir $(BUILDDIR)
# Set the current directory as the only source search path (for -u)
BSCFLAGS_EXT += -p .
# Specify a vsearch path to replace the default
# (to avoid warnings about the directory not existing)
BSCFLAGS_EXT += -vsearch $(BUILDDIR)
# Increase the RTS stack
#BSCFLAGS_EXT += +RTS -K32M -RTS

BSCFLAGS ?= $(BSCFLAGS_EXT)

BSC ?= $(BINDIR)/bsc

