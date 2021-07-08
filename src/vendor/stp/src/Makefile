SRCTOP=.
include Makefile.common

STPDIR=..
LIB_DIR=$(STPDIR)/lib
INCLUDE_DIR=$(STPDIR)/include

HEADERS=c_interface/*.h

# BSD cp does not have the -d flag
ifneq ($(OSTYPE), Linux)
CP = cp -Rf
else
CP = cp -df
endif

ifeq ($(OSTYPE), Darwin)
LIBRARIES=lib/libstp.dylib
SNAME = libstp.dylib
else
LIBRARIES=lib/libstp.so.1 lib/libstp.so
SNAME = libstp.so.1
endif

.PHONY: all
all: $(LIBRARIES)


# The CC command for linking static libraries into a library is tricky
# and different for Linux and Mac OS
ifeq ($(OSTYPE), Darwin)
LIBCCARGS =     c_interface/c_interface.o \
		extlib-constbv/libconstantbv.a extlib-abc/libabc.a \
		to-sat/libtosat.a \
		STPManager/libstpmgr.a simplifier/libsimplifier.a \
		absrefine_counterexample/libabstractionrefinement.a \
		AST/libast.a \
		printer/libprinter.a \
		sat/libminisat.a \
		cpp_interface/libcppinterface.a \
		parser/libparser.a \
		main/libmain.a
else
LIBCCARGS =     -Lto-sat -Wl,--whole-archive -ltosat -Wl,--no-whole-archive \
		c_interface/c_interface.o \
		extlib-constbv/libconstantbv.a extlib-abc/libabc.a \
		STPManager/libstpmgr.a simplifier/libsimplifier.a \
		absrefine_counterexample/libabstractionrefinement.a \
		AST/libast.a \
		printer/libprinter.a \
		sat/libminisat.a \
		cpp_interface/libcppinterface.a \
		parser/libparser.a \
		main/libmain.a
endif

lib/$(SNAME):  c_interface/c_interface.o \
		extlib-constbv/libconstantbv.a extlib-abc/libabc.a \
		to-sat/libtosat.a \
		STPManager/libstpmgr.a simplifier/libsimplifier.a \
		absrefine_counterexample/libabstractionrefinement.a \
		AST/libast.a \
		printer/libprinter.a \
		sat/libminisat.a \
		cpp_interface/libcppinterface.a \
		parser/libparser.a \
		main/libmain.a
	mkdir -p $(@D)
	$(RM) $@
	@# For some reason, this line doesn't work
	@# $(CXX) $(CFLAGS) $(SHAREDFLAG) -o $@ $^
	@# We use --whole-archive to ensure that all symbols in to-sat are used
	$(CXX) $(CFLAGS) $(SHAREDFLAG)  -Wl,$(SONAMEFLAG),$(SNAME) -o $@ $(LIBCCARGS)

ifneq ($(OSTYPE), Darwin)
lib/libstp.so: lib/libstp.so.1
	-rm -f $@
	(cd lib; ln -s libstp.so.1 libstp.so)
endif


# During the build of AST some classes are built that most of the other
# classes depend upon. So in a parallel make, AST should be made first.
c_interface/c_interface.o \
STPManager/libstpmgr.a printer/libprinter.a \
absrefine_counterexample/libabstractionrefinement.a \
to-sat/libtosat.a simplifier/libsimplifier.a \
cpp_interface/libcppinterface.a \
extlib-constbv/libconstantbv.a extlib-abc/libabc.a parser/libparser.a \
main/libmain.a: AST/libast.a

sat/libminisat.a: MAKEGOALS=core

c_interface/c_interface.o \
AST/libast.a STPManager/libstpmgr.a printer/libprinter.a \
absrefine_counterexample/libabstractionrefinement.a \
to-sat/libtosat.a sat/libminisat.a simplifier/libsimplifier.a \
extlib-constbv/libconstantbv.a extlib-abc/libabc.a \
cpp_interface/libcppinterface.a \
parser/libparser.a main/libmain.a:
	$(MAKE) -C $(@D) $(MAKEGOALS)

####

.PHONY: install
install: all
	mkdir -p $(LIB_DIR)
	mkdir -p $(INCLUDE_DIR)
	$(CP) $(LIBRARIES) $(LIB_DIR)
	$(CP) $(HEADERS) $(INCLUDE_DIR)
	mv $(INCLUDE_DIR)/c_interface.h $(INCLUDE_DIR)/stp_c_interface.h

.PHONY: clean
clean:
	rm -rf lib
	$(MAKE) clean -C AST
	$(MAKE) clean -C STPManager	
	$(MAKE) clean -C printer
	$(MAKE) clean -C extlib-constbv
	$(MAKE) clean -C extlib-abc
	$(MAKE) clean -C simplifier
	$(MAKE) clean -C absrefine_counterexample
	$(MAKE) clean -C to-sat
	$(MAKE) clean -C sat
	$(MAKE) clean -C c_interface	
	$(MAKE) clean -C cpp_interface	
	$(MAKE) clean -C parser
	$(MAKE) clean -C main

.PHONY: full_clean
full_clean: clean
	$(RM) -R $(LIB_DIR)
	$(RM) -R $(INCLUDE_DIR)

