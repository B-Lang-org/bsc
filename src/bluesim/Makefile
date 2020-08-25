PWD:=$(shell pwd)
TOP:=$(PWD)/../..

INSTALL ?= install

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/Bluesim

COMPDIR=$(TOP)/src/comp

.PHONY: all
all: install

# -------------------------

# These get copied to the inst/lib/Bluesim area
HEADERS = bluesim_kernel_api.h \
          bluesim_types.h \
          bluesim_primitives.h \
          bluesim_systemc.h \
          bluesim_probes.h \
          bs_wide_data.h \
          bs_prim_ops.h \
          bs_prim_mod_reg.h bs_prim_mod_wire.h bs_prim_mod_probe.h \
          bs_prim_mod_fifo.h bs_prim_mod_regfile.h bs_prim_mod_bram.h \
          bs_prim_mod_counter.h \
          bs_prim_mod_clockgen.h \
          bs_prim_mod_synchronizers.h \
          bs_prim_mod_gatedclock.h \
          bs_prim_mod_clockmux.h \
          bs_prim_mod_resets.h \
          bs_reset.h \
          bs_symbol.h \
          bs_system_tasks.h \
          bs_mem_defines.h bs_mem_file.h bs_range_tracker.h \
          bs_vcd.h bs_module.h bs_target.h \
          bs_model.h

# These ld export maps get copies to the inst/lib/Bluesim area
LINKFILES = bs_elf_export_map.txt \
            bs_mach-o_export_map.txt

# -------------------------

CFLAGS += -Wall -Wextra -Werror \
	-Wmissing-prototypes \
	-Wstrict-prototypes \
	-Wpointer-arith \
	-Wshadow \
	-Wcast-qual \
	-Wno-unused-parameter \
	-g \
	-std=c99 \
        -D_FILE_OFFSET_BITS=64 \
	-fPIC
CXXFLAGS += -Wall -Wextra -Werror \
	-Wpointer-arith \
	-Wshadow \
	-Wcast-qual \
	-Wno-unused-parameter \
	-g \
	-D_ISOC99_SOURCE \
	-std=c++11 \
        -D_FILE_OFFSET_BITS=64 \
        -fno-rtti \
	-fPIC

# Compares two dotted numeric strings (e.g 2.3.16.1) for $1 >= $2
define version_ge
$(findstring TRUE,$(shell bash -c 'sort -cu -t. -k1,1nr -k2,2nr -k3,3nr -k4,4nr <(echo -e "$2\n$1") 2>&1 || echo TRUE'))
endef

glibcversion := $(shell ldd --version | head -1 | awk '{print $$NF}')
ifeq ($(call version_ge,$(glibcversion),2.20),TRUE)
CFLAGS += -D_DEFAULT_SOURCE
CXXFLAGS += -D_DEFAULT_SOURCE
else
CFLAGS += -D_SVID_SOURCE
CXXFLAGS += -D_SVID_SOURCE
endif

COPT ?= -O3
CDEBUG ?= -UUSE_ENTER
CFLAGS += $(PROF) $(COPT) $(CDEBUG)
CXXFLAGS += $(PROF) $(COPT) $(CDEBUG) 

# Description of library of Bluesim primitives
LIB_PRIM = libbsprim.a
PRIM_OBJS = prim_ops.o wide_data.o mem_alloc.o target.o \
            prim_mod_reg.o prim_mod_wire.o prim_mod_probe.o \
            prim_mod_fifo.o prim_mod_regfile.o prim_mod_bram.o \
            prim_mod_counter.o \
            prim_mod_clockgen.o \
            prim_mod_synchronizers.o \
            prim_mod_gatedclock.o \
            prim_mod_resets.o \
            dollar_display.o dollar_dumpvars.o dollar_plusargs.o \
            dollar_stop_finish.o dollar_time.o \
            mem_file.o module.o portability.o \
            rand32.o

# Description of Bluesim kernel library
LIB_KERNEL = libbskernel.a
KERNEL_OBJS = kernel.o event_queue.o priority.o symbol.o \
              reset.o plusargs.o vcd.o portability.o

LIBS = $(LIB_PRIM) $(LIB_KERNEL)

vpath %.cxx ../

%.o:%.cxx
	$(CXX) -E -MM $< > $*.p
	cp $*.p $*.d; \
	sed -e 's/#.*//' -e 's/^[^:]*: *//' -e 's/ *\\$$//' \
	    -e '/^$$/ d' -e 's/$$/ :/' < $*.p >> $*.d; \
	rm -f $*.p
	$(CXX) $(CXXFLAGS) -c -o $@ $<

# -------------------------

$(LIB_PRIM): version $(PRIM_OBJS)
	$(RM) $(LIB_PRIM)
	$(AR) cr $(LIB_PRIM) $(PRIM_OBJS)

$(LIB_KERNEL): version $(KERNEL_OBJS)
	$(RM) $(LIB_KERNEL)
	$(AR) cr $(LIB_KERNEL) $(KERNEL_OBJS)

.PHONY: version
version:
	./gen_version_h $(COMPDIR)/BuildVersion.hs > version.h

# Static check of the header files before releasing them.
# Don't include headers which require systemC.
.PHONY: test-headers
test-headers:
	$(RM) test_hdr.cxx
	for hdr in $(HEADERS); do \
	  if [ $$hdr != "bluesim_systemc.h" ]; then \
	    echo "#include \"$$hdr\"" >> test_hdr.cxx ; \
	  fi ; \
	done
	$(CXX) -std=c++11 -c -o /dev/null test_hdr.cxx

.PHONY: install
install: $(LIBS) test-headers
	$(INSTALL) -m 755 -d $(INSTALLDIR)
	$(INSTALL) -m 644 $(HEADERS) $(INSTALLDIR)
	$(INSTALL) -m 644 $(LINKFILES) $(INSTALLDIR)
	$(INSTALL) -m 644 $(LIBS) $(INSTALLDIR)

.PHONY: clean
clean:
	$(RM) test_hdr.cxx version.h
	$(RM) *.o *.p *.d $(LIBS)

.PHONY: full_clean
full_clean: clean

TAGS:	*.h *.c *.cxx
	etags *.h *.c *.cxx

# include dependency information
DEPEND_OBJS = $(PRIM_OBJS) $(KERNEL_OBJS)

-include $(DEPEND_OBJS:.o=.d)

# -------------------------
