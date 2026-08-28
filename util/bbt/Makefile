PREFIX ?= $(shell pwd)/../../inst

# Ensure ghcup-managed cabal is on PATH even when make is invoked with a
# minimal PATH (e.g. from the top-level install-src).
export PATH := $(HOME)/.ghcup/bin:$(HOME)/.cabal/bin:$(PATH)

CABAL ?= cabal

.PHONY: install
install:
	$(CABAL) install --installdir=$(PREFIX)/bin --overwrite-policy=always --install-method=copy exe:bbt

.PHONY: clean
clean:
	$(CABAL) clean
