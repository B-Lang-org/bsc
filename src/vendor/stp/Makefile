TOP=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all install clean full_clean

# install copies the library under its soname and adds the link name beside
# it, so that a build may link the installed copy by name.

ifeq ($(STP_STUB),)
SRC = src
else
SRC = src_stub
endif

ifeq ($(OSTYPE), Darwin)
SNAME=libstp.dylib
LNAME=libstp.dylib
else
SNAME=libstp.so.1
LNAME=libstp.so
endif

all: install

install:
	$(MAKE) -C $(SRC) install
	ln -fsn HaskellIfc include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/$(SNAME) $(PREFIX)/lib/SAT
	[ "$(SNAME)" = "$(LNAME)" ] || ln -sfn $(SNAME) $(PREFIX)/lib/SAT/$(LNAME)

clean:
	$(MAKE) -C $(SRC) clean

full_clean:
	$(MAKE) -C $(SRC) full_clean
	rm -f include_hs
