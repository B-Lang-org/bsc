TOP:=../..

PREFIX?=$(TOP)/inst

.PHONY: all clean full_clean intall

VERSION = v2.6

all: install

install:
	$(MAKE) -C $(VERSION) install
	ln -fsn $(VERSION)/include
	ln -fsn $(VERSION)/lib
	ln -fsn $(VERSION)/include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/* $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -f include lib include_hs

