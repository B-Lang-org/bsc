PWD := $(shell pwd)
TOP := $(PWD)/..

PREFIX ?= $(TOP)/inst

# -------------------------

INSTALL ?= install -c

RM = rm -f

# -------------------------
# Options

# Set this to 1 if the Asciidoctor tool is not available.
# PDF and HTML versions of the release notes will not be installed,
# only the raw AsciiDoc file.
#
NOASCIIDOCTOR ?= 0

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

INSTALLFILES = ReleaseNotes.adoc

ifeq ($(NOASCIIDOCTOR),0)
INSTALLFILES += ReleaseNotes.html
INSTALLFILES += ReleaseNotes.pdf
endif

# -------------------------

.PHONY: install
install: install-README install-COPYING install-NOTES

$(PREFIX):
	$(INSTALL) -m 755 -d $(PREFIX)

.PHONY: install-README
install-README: $(PREFIX) tarball-README
	$(INSTALL) -m 644  tarball-README  $(PREFIX)/README

.PHONY: install-COPYING
install-COPYING: $(PREFIX) $(LICFILES) tarball-COPYING
	$(INSTALL) -m 755 -d $(PREFIX)/LICENSES
	$(INSTALL) -m 644  $(LICFILES)  $(PREFIX)/LICENSES/
	$(INSTALL) -m 644  tarball-COPYING  $(PREFIX)/COPYING

.PHONY: install-NOTES
install-NOTES: $(PREFIX) $(INSTALLFILES)
	$(INSTALL) -m 644  $(INSTALLFILES)  $(PREFIX)/

# -----

ReleaseNotes.html: ReleaseNotes.adoc
	asciidoctor ReleaseNotes.adoc

ReleaseNotes.pdf: ReleaseNotes.adoc
	asciidoctor-pdf --theme=default-with-font-fallbacks ReleaseNotes.adoc

# -----

.PHONY: clean
clean:
	$(RM) ReleaseNotes.html ReleaseNotes.pdf

.PHONY: full_clean
full_clean: clean

# -------------------------
