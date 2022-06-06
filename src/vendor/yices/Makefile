TOP:=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean install

VER_MAJ = 2
VER_MIN = 6
PATCH_LEVEL = 4
VERSION = v$(VER_MAJ).$(VER_MIN)

all: install

ifeq ($(OSTYPE), Darwin)
SNAME=libyices.$(VER_MAJ).dylib
else
SNAME=libyices.so.$(VER_MAJ).$(VER_MIN)
SNAME_FULL=libyices.so.$(VER_MAJ).$(VER_MIN).$(PATCH_LEVEL)
endif

install:
	$(MAKE) -C $(VERSION) install
	ln -fsn $(VERSION)/include
	ln -fsn $(VERSION)/lib
	ln -fsn $(VERSION)/include_hs
ifneq ($(OSTYPE), Darwin)
	ln -fs  $(SNAME_FULL) lib/$(SNAME)
endif
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/$(SNAME) $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -f include lib include_hs

