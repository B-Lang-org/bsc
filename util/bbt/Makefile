PREFIX ?= $(shell pwd)/../../inst

CABAL ?= cabal

.PHONY: install
install:
	$(CABAL) install --installdir=$(PREFIX)/bin --overwrite-policy=always exe:bbt

.PHONY: clean
clean:
	$(CABAL) clean
