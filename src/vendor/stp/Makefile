TOP=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all install clean full_clean

ifneq ($(STP_STUB),) # STP_STUB didn't work for 3 years anyway
$(error STP_STUB is deprecated: Use STP_USE_LIB=disable instead)
endif

ifeq ($(STP_USE_LIB),) # use default
STP_USE_LIB=included
endif

define ispath
$(shell echo "$1" | grep -E "^/*")
endef

ifeq ($(STP_USE_LIB),included)      # compile from provided source
SRC = src
else ifeq ($(STP_USE_LIB),disable)  # disable STP at runtime
SRC = src_stub
else ifeq ($(STP_USE_LIB),system)   # use system STP
SRC = src_sys
STP_LIBPATH = /usr/lib/
export STP_LIBPATH
else ifneq ($(call ispath,"$(STP_USE_LIB)"),) # use STP at the absolute path provided by STP_USE_LIB
SRC = src_sys
STP_LIBPATH = $(STP_USE_LIB)
export STP_LIBPATH
else # unknown option for STP_USE_LIB
$(error Unknown option for STP_USE_LIB: $(STP_USE_LIB))
endif

ifeq ($(OSTYPE), Darwin)
SNAME=libstp.dylib
else
SNAME=libstp.so.1
endif

all: install

install:
	$(MAKE) -C $(SRC) install
	ln -fsn HaskellIfc include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/$(SNAME) $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(SRC) clean

full_clean:
	$(MAKE) -C $(SRC) full_clean
	rm -f include_hs
