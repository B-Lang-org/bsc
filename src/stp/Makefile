TOP=../..
PREFIX?=$(TOP)/inst

.PHONY: all install clean full_clean

SRC = src

all: install

install:
	make -C $(SRC) install
	ln -fsT HaskellIfc include_hs
	install -m 755 -d $(PREFIX)/lib/SAT
	install -m 644 lib/* $(PREFIX)/lib/SAT

clean:
	make -C $(SRC) clean

full_clean:
	make -C $(SRC) full_clean
	rm -f include_hs
