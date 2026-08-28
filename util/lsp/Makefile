SHELL    := /bin/bash
PWD      := $(shell pwd)
REPO_ROOT := $(abspath $(PWD)/../..)
PREFIX   ?= $(REPO_ROOT)/inst
BINDIR    = $(PREFIX)/bin
DOCDIR    = $(PREFIX)/doc/bluespec

# Ensure ghcup-managed tools (cabal, ghc-9.10.1, etc.) are on PATH even when
# make is invoked with a minimal PATH (e.g. from the top-level install-src).
export PATH := $(HOME)/.ghcup/bin:$(HOME)/.cabal/bin:$(PATH)
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

.PHONY: install-bbt
install-bbt:
	cd $(BBT_CABAL) && cabal build exe:bbt
	$(INSTALL) -m 755 -d $(BINDIR)
	$(INSTALL) -m 755 $$(cd $(BBT_CABAL) && cabal list-bin bbt) $(BINDIR)/bbt

# Install the VSCode extension.  Requires Node.js / npm.
# Skips gracefully if npm is not available.
# Also updates ~/.vscode/extensions/extensions.json so VS Code recognises the
# manually-deployed extension without needing a marketplace install.
.PHONY: install-vscode-ext
install-vscode-ext: install install-bbt
	@if command -v npm >/dev/null 2>&1; then \
	  echo "Installing vscode-bluespec extension to $(VSCODE_EXT_DIR)..."; \
	  cd vscode-bluespec && npm install --silent; \
	  rm -rf "$(VSCODE_EXT_DIR)"; \
	  mkdir -p "$(VSCODE_EXT_DIR)"; \
	  cp -r extension.js \
	        language-configuration.json \
	        language-configuration-bsv.json \
	        package.json syntaxes node_modules "$(VSCODE_EXT_DIR)/"; \
	  python3 -c "\
import json, os, time; \
ext_json = os.path.expanduser('~/.vscode/extensions/extensions.json'); \
exts = []; \
os.makedirs(os.path.dirname(ext_json), exist_ok=True); \
(open(ext_json).read() and exts.__init__(json.load(open(ext_json)))) if os.path.exists(ext_json) else None; \
exts = [e for e in exts if e.get('identifier', {}).get('id') != 'bsc-lsp.vscode-bluespec']; \
exts.append({'identifier': {'id': 'bsc-lsp.vscode-bluespec'}, 'version': '0.0.1', 'location': {'scheme': 'file', 'path': '$(VSCODE_EXT_DIR)'}, 'relativeLocation': 'vscode-bluespec-0.0.1', 'metadata': {'installedTimestamp': int(time.time() * 1000)}}); \
open(ext_json, 'w').write(json.dumps(exts, indent=2) + '\n'); \
print('Updated', ext_json) \
"; \
	  echo "Done. Restart VS Code (or run 'Developer: Reload Window') to activate."; \
	  echo "Make sure $(BINDIR) is on your PATH, or set bluespec.serverPath in VS Code settings."; \
	else \
	  echo "npm not found — skipping VSCode extension install."; \
	  echo "To install manually: cd vscode-bluespec && npm install && ./setup.sh"; \
	fi

# Build a self-contained .vsix extension package.
# Uses a pure-Python builder (mk-vsix.py) so Node >=20 / vsce is not required.
# Output: vscode-bluespec/vscode-bluespec-$(EXT_VERSION).vsix
EXT_VERSION ?= 0.0.1
VSIX_OUT    := $(PWD)/vscode-bluespec/vscode-bluespec-$(EXT_VERSION).vsix

.PHONY: package-vsix
package-vsix:
	@if command -v npm >/dev/null 2>&1; then \
	  cd vscode-bluespec && npm install --silent; \
	fi
	@echo "Packaging $(VSIX_OUT)..."
	@python3 $(PWD)/vscode-bluespec/mk-vsix.py \
	         $(PWD)/vscode-bluespec \
	         $(VSIX_OUT)
	@echo "Install with: code --install-extension $(VSIX_OUT)"

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

# -------------------------
# Documentation
# -------------------------

# Build bs-docgen and generate the full documentation site into $(DOCDIR).
# Includes both the stdlib API docs (from src/Libraries) and the converted
# BH_lang.tex reference manual.  Output goes to inst/doc/bluespec/ by default,
# which is already gitignored via 'inst' in the top-level .gitignore.
#
# Usage:
#   make docs                   # generate to inst/doc/bluespec/
#   make docs DOCDIR=/tmp/docs  # generate to a custom location
#   make install-docs           # same, but also prints the output path

BBT_CABAL    := $(REPO_ROOT)/util/bbt
DOCGEN_CABAL := $(REPO_ROOT)/util/docgen
BSC_DOC_DIR  := $(REPO_ROOT)/doc
LIB_DIRS     := $(REPO_ROOT)/src/Libraries

.PHONY: docs
docs:
	@cd $(DOCGEN_CABAL) && cabal build exe:bs-docgen -v0
	$(eval DOCGEN_BIN := $(shell cd $(DOCGEN_CABAL) && cabal list-bin bs-docgen 2>/dev/null))
	@mkdir -p $(DOCDIR)
	$(DOCGEN_BIN) \
	  --lib-dir $(LIB_DIRS) \
	  $(if $(wildcard $(BSC_DOC_DIR)),--bsc-doc-dir $(BSC_DOC_DIR),) \
	  --out $(DOCDIR)

.PHONY: install-docs
install-docs: docs
	@echo "[docgen] Documentation installed to $(DOCDIR)"

.PHONY: clean
clean:
	cd bs-lsp && cabal clean
	cd bs-parser && cabal clean
	rm -f bs-lsp-bin
