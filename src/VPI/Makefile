PWD:=$(shell pwd)
TOP:=$(PWD)/../..

include $(TOP)/platform.mk

INSTALL ?= install

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/VPI

.PHONY:	all
all: install

# -------------------------

# These get copied to the inst/lib/VPI area
HEADERS = bdpi.h vpi_user.h

# -------------------------

CFLAGS += -Wall \
	-Wmissing-prototypes \
	-Wpointer-arith \
	-Wshadow \
	-Wcast-qual \
	-Werror \
	-Wno-shadow \
	-g \
	-std=c99 \
	-fPIC \
# vpi_user.h fails this check
#	-Wstrict-prototypes

COPT ?= -O3
CDEBUG ?=
CFLAGS += $(PROF) $(COPT) $(CDEBUG)

ifeq ($(OSTYPE), Darwin)
# for Mac OS X, declare that the binary is dynamic and undefined references
# will be looked up later when the library is linked
LIBBDPI=libbdpi.dylib
LDFLAGS = -dynamiclib -Wl,-install_name,@rpath/$(LIBBDPI),-undefined,dynamic_lookup
else
LIBBDPI=libbdpi.so
LDFLAGS = -shared -Wl,-soname,$(LIBBDPI)
endif

vpath %.c ../

%.o:%.c
	$(CC) -E -MM $< > $*.p
	cp $*.p $*.d; \
	sed -e 's/#.*//' -e 's/^[^:]*: *//' -e 's/ *\\$$//' \
	    -e '/^$$/ d' -e 's/$$/ :/' < $*.p >> $*.d; \
	rm -f $*.p
	$(CC) $(CFLAGS) -c -o $@ $<

# -------------------------

$(LIBBDPI): libbdpi.o
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

# Static check of the header files before releasing them.
.PHONY: test-headers
test-headers:
	$(RM) test_hdr.c
	for hdr in $(HEADERS); do \
          echo "#include \"$$hdr\"" >> test_hdr.c ; \
	done
	$(CC) -c -o /dev/null test_hdr.c

.PHONY: install
install: $(HEADERS) $(LIBBDPI) test-headers
	$(INSTALL) -m 755 -d $(INSTALLDIR)
	$(INSTALL) -m 644 $(HEADERS) $(INSTALLDIR)
	$(INSTALL) -m 644 $(LIBBDPI) $(INSTALLDIR)

.PHONY: clean
clean:
	$(RM) test_hdr.c
	$(RM) *.o *.d $(LIBBDPI)

.PHONY: full_clean
full_clean: clean

TAGS:	*.h *.c
	etags *.h *.c

# include dependency information
DEPEND_OBJS = libbdpi.o

-include $(DEPEND_OBJS:.o=.d)

# -------------------------
