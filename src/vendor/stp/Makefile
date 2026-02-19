TOP=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all install clean full_clean

ifeq ($(STP_STUB),)
SRC = src
else
SRC = src_stub
SNAME += lib/libstp_stub.so
endif

ifeq ($(OSTYPE), Darwin)
SNAME = lib/libstp.dylib
else
SNAME += lib/libstp.so.1
endif

all: install

install:
	$(MAKE) -C $(SRC) install
	ln -fsn HaskellIfc include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 $(SNAME) $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(SRC) clean

full_clean:
	$(MAKE) -C $(SRC) full_clean
	rm -f include_hs
