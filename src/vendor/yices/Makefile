TOP:=../../..
include $(TOP)/platform.mk

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean install

# install copies the library under its soname and adds the link name beside
# it, so that a build may link the installed copy by name.

VER_MAJ = 2
VER_MIN = 6
VERSION = v$(VER_MAJ).$(VER_MIN)

all: install

ifeq ($(OSTYPE), Darwin)
SNAME=libyices.$(VER_MAJ).dylib
LNAME=libyices.dylib
else
SNAME=libyices.so.$(VER_MAJ).$(VER_MIN)
LNAME=libyices.so
endif

install:
	$(MAKE) -C $(VERSION) install
	ln -fsn $(VERSION)/include
	ln -fsn $(VERSION)/lib
	ln -fsn $(VERSION)/include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/$(SNAME) $(PREFIX)/lib/SAT
	ln -sfn $(SNAME) $(PREFIX)/lib/SAT/$(LNAME)

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -f include lib include_hs

