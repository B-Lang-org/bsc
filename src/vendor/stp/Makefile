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

ifeq ($(OSTYPE), Darwin)
SO=dylib
else
SO=so
endif

ifeq ($(STP_USE_LIB),included)      # compile from provided source
    SRC = src
    ifeq ($(OSTYPE), Darwin)
        SNAME=libstp_incl.dylib
    else
        SNAME=libstp_incl.so.1
    endif
else ifeq ($(STP_USE_LIB),disable)  # disable STP at runtime
    SRC = src_stub
    SNAME=libstp_disabled.$(SO)
else ifeq ($(STP_USE_LIB),system)   # use system STP
    SRC = src_sys
    ifeq ($(OSTYPE), Darwin)
        SNAME=libstp_sys.dylib
        STP_LIBPATH = /usr/local/opt/stp@
    else # Linux
        SNAME=libstp_sys.so
        STP_LIBPATH=$(shell find /usr/lib/ -name "libstp.so*" -type f -print0 | tr '\0' '\n' | grep "/[a-z0-9.]*$$" | head -n 1)
        ifeq ($(STP_LIBPATH),)
            $(error No valid library found in /usr/lib)
        endif
    endif
    export STP_LIBPATH
else ifneq ($(call ispath,"$(STP_USE_LIB)"),) # use STP at the absolute path provided by STP_USE_LIB
    SRC = src_sys
    SNAME=libstp_custom.$(SO)
    STP_LIBPATH = $(STP_USE_LIB)
    export STP_LIBPATH
else # unknown option for STP_USE_LIB
    $(error Unknown option for STP_USE_LIB: $(STP_USE_LIB))
endif
export SNAME

all: install

install:
	$(MAKE) -C $(SRC) install
	ln -fsn HaskellIfc include_hs
	@# necessary for bsc linker (src/comp/Makefile:51)
	ln -s "$(SNAME)" lib/libstp.$(SO)
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 "lib/$(SNAME)" $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(SRC) clean

full_clean:
	$(MAKE) -C $(SRC) full_clean
	rm -f include_hs
