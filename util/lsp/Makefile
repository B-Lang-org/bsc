SHELL    := /bin/bash
PWD      := $(shell pwd)
REPO_ROOT := $(abspath $(PWD)/../..)
PREFIX   ?= $(REPO_ROOT)/inst
BINDIR    = $(PREFIX)/bin
INSTALL  ?= install -c

# VSCode extension install directory
VSCODE_EXT_DIR ?= $(HOME)/.vscode/extensions/vscode-bluespec-0.0.1

.PHONY: all
all:
	cd bs-lsp && cabal build exe:bs-lsp
	cp $$(cd bs-lsp && cabal list-bin bs-lsp) $(PWD)/bs-lsp-bin

.PHONY: install
install: all
	$(INSTALL) -m 755 -d $(BINDIR)
	$(INSTALL) -m 755 bs-lsp-bin $(BINDIR)/bs-lsp

# Install the VSCode extension.  Requires Node.js / npm.
# Skips gracefully if npm is not available.
.PHONY: install-vscode-ext
install-vscode-ext:
	@if command -v npm >/dev/null 2>&1; then \
	  echo "Installing vscode-bluespec extension to $(VSCODE_EXT_DIR)..."; \
	  cd vscode-bluespec && npm install --silent; \
	  rm -rf "$(VSCODE_EXT_DIR)"; \
	  mkdir -p "$(VSCODE_EXT_DIR)"; \
	  cp -r extension.js language-configuration.json package.json syntaxes node_modules "$(VSCODE_EXT_DIR)/"; \
	  echo "Done. Restart VS Code (or run 'Developer: Reload Window') to activate."; \
	  echo "Make sure $(BINDIR) is on your PATH, or set bluespec.serverPath in VS Code settings."; \
	else \
	  echo "npm not found — skipping VSCode extension install."; \
	  echo "To install manually: cd vscode-bluespec && npm install && ./setup.sh"; \
	fi

# -------------------------
# Tests
# -------------------------

.PHONY: test
test: test-parser test-lsp

# Run the bs-parser against all .bs files in the bsc repository
# (standard library + testsuite).  Reports pass/fail counts.
# Exits zero for now — known parser gaps are tracked in PLAN/PHASE2.md.
# Goal: 100% pass rate (all .bs files in the repo are syntactically valid).
.PHONY: test-parser
test-parser:
	@cd bs-parser && cabal build exe:bs-parser 2>&1 | grep -v "^Up to date" | grep -v "^Build" || true
	@PARSER=$$(cd bs-parser && cabal list-bin bs-parser); \
	PASS=0; FAIL=0; \
	while IFS= read -r f; do \
	  if "$$PARSER" check "$$f" 2>/dev/null | grep -q "^OK:"; then \
	    PASS=$$((PASS + 1)); \
	  else \
	    echo "FAIL: $$f"; \
	    FAIL=$$((FAIL + 1)); \
	  fi; \
	done < <(find "$(REPO_ROOT)/src/Libraries" "$(REPO_ROOT)/testsuite" \
	           -name "*.bs" -not -path "*/dist-newstyle/*" 2>/dev/null | sort); \
	echo ""; \
	echo "Parser tests: $$PASS passed, $$FAIL failed"

# Run the LSP test suite.  Uses bsc/src/Libraries as the standard
# library source (no Bazel or BLUESPECDIR required).
.PHONY: test-lsp
test-lsp:
	cd bs-lsp && BLUESPEC_SRC="$(REPO_ROOT)" cabal test

.PHONY: clean
clean:
	cd bs-lsp && cabal clean
	cd bs-parser && cabal clean
	rm -f bs-lsp-bin
