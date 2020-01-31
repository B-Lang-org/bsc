TOP:=../..

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean intall

VERSION = v2.6

all: install

install:
	make -C $(VERSION) install
	ln -fsT $(VERSION)/include    include
	ln -fsT $(VERSION)/lib        lib
	ln -fsT $(VERSION)/include_hs include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/* $(PREFIX)/lib/SAT

clean:
	make -C $(VERSION) clean

full_clean:
	make -C $(VERSION) full_clean
	rm -f include lib include_hs

