PWD := $(shell pwd)
TOP := $(PWD)/..

PREFIX ?= $(TOP)/inst

# -------------------------

INSTALL ?= install -c

RM = rm -f

# -------------------------

LICDIR = ../LICENSES

LICFILES = $(addprefix $(LICDIR)/, \
	LICENSE.ghc \
	LICENSE.hbc \
	LICENSE.parsec \
	LICENSE.stp \
	LICENSE.stp_components \
	LICENSE.yices \
	LICENSE.yices-painless \
	)

# -------------------------

.PHONY: install
install: install-README install-COPYING install-NOTES

$(PREFIX):
	$(INSTALL) -m 755 -d $(PREFIX)

.PHONY: install-README
install-README: $(PREFIX) tarball-README
	$(INSTALL) -m 644  tarball-README  $(PREFIX)/README

.PHONY: install-COPYING
install-COPYING: $(PREFIX) $(LICFILES)
	$(INSTALL) -m 755 -d $(PREFIX)/LICENSES
	$(INSTALL) -m 644  $(LICFILES)  $(PREFIX)/LICENSES/

.PHONY: install-NOTES
install-NOTES: $(PREFIX) ReleaseNotes.adoc ReleaseNotes.html ReleaseNotes.pdf
	$(INSTALL) -m 644  ReleaseNotes.adoc  $(PREFIX)/
	$(INSTALL) -m 644  ReleaseNotes.html  $(PREFIX)/
	$(INSTALL) -m 644  ReleaseNotes.pdf   $(PREFIX)/

# -----

ReleaseNotes.html: ReleaseNotes.adoc
	asciidoctor ReleaseNotes.adoc

ReleaseNotes.pdf: ReleaseNotes.adoc
	asciidoctor-pdf ReleaseNotes.adoc

# -----

.PHONY: clean
clean:
	$(RM) ReleaseNotes.html ReleaseNotes.pdf

.PHONY: full_clean
full_clean: clean

# -------------------------
