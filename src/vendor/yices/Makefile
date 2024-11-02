TOP:=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean install

VER_MAJ = 2
VER_MIN = 6
VERSION = v$(VER_MAJ).$(VER_MIN)

all: install

$(info OSTYPE: $(OSTYPE))
ifeq ($(OSTYPE), Darwin)
SNAME=lib/libyices.$(VER_MAJ).dylib
else ifeq ($(OSTYPE), Mingw)
SNAME=$(VERSION)/yices2-inst/bin/libyices.dll
else
SNAME=lib/libyices.so.$(VER_MAJ).$(VER_MIN)
endif

install:
	$(MAKE) -C $(VERSION) install
	rm -rf include lib include_hs
	ln -fsn $(VERSION)/include
	ln -fsn $(VERSION)/lib
	ln -fsn $(VERSION)/include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 $(SNAME) $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -rf include lib include_hs

