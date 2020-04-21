TOP=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all install clean full_clean

ifeq ($(STP_STUB),)
SRC = src
else
SRC = src_stub
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
