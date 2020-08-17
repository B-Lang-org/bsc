TOP:=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean install

VER_MAJ = 2
VER_MIN = 6
VERSION = v$(VER_MAJ).$(VER_MIN)

all: install

ifeq ($(OSTYPE), Darwin)
SNAME=libyices.$(VER_MAJ).dylib
else
SNAME=libyices.so.$(VER_MAJ).$(VER_MIN)
endif

install:
	$(MAKE) -C $(VERSION) install
	ln -fsn $(VERSION)/include
	ln -fsn $(VERSION)/lib
	ln -fsn $(VERSION)/include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/$(SNAME) $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -f include lib include_hs

