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
	# add missing symlink libyices.so.2.6{->2}
	ln -fsn libyices.so.2.6.2 lib/libyices.so.2.6
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/* $(PREFIX)/lib/SAT

clean:
	$(MAKE) -C $(VERSION) clean

full_clean:
	$(MAKE) -C $(VERSION) full_clean
	rm -f include lib include_hs

