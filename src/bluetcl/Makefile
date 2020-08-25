PWD:=$(shell pwd)
TOP:=$(PWD)/../..

PREFIX?=$(TOP)/inst
INSTALLDIR = $(PREFIX)/lib/tcllib/bluespec

TCLSH = $(shell $(TOP)/platform.sh tclsh)

FILES = \
	tclIndex \
	pkgIndex.tcl \
	bluespec.tcl \

# tcl files which need each proc listed in tclIndex
# utils.tcl is really a package, but some initization code require it
TCLFILES = \
	utils.tcl \

# tcl packages
PACKAGES = \
        BluesimP.tcl \

# top level user scripts
EXEFILES = \
	bluesim.tcl \
	makedepend.tcl \

.PHONY: all
all: tclIndex

# pkg_mkIndex.tcl is produced here
.PHONY: tclIndex
tclIndex: *.tcl
	${TCLSH} ./tclIndex.sh "$(TCLFILES)" "$(PACKAGES)"

.PHONY: install
install: tclIndex
	install -d -m755 $(INSTALLDIR)
	install -m644 $(FILES) $(PACKAGES) $(TCLFILES) $(INSTALLDIR)
	install -m755 $(EXEFILES) $(INSTALLDIR)

.PHONY: clean
clean:
	rm -f tclIndex pkg_mkIndex.tcl pkgIndex.tcl

.PHONY: full_clean
full_clean: clean

