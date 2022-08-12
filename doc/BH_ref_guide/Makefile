RM=rm
INSTALL?=install -c

DOC=BH_lang

PWD := $(shell pwd)
TOP := $(PWD)/../..

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/doc
INSTALLNAME=BH_lang_ref_guide

.PHONY: all
all:	$(DOC).pdf

.PHONY: clean
clean:
	${RM} -f *.pdf  *.blg *.bbl *.aux *.log *.toc *.idx *.ind *.ilg *.out

.PHONY: full_clean
full_clean: clean
	${RM} -f *.log *.aux *.blg *.bbl *.out *.toc *.idx *.ind *.ilg

$(DOC).pdf: $(DOC).tex  version.tex
	$(RM) -f *.log *.aux *.blg *.bbl *.out *.toc *.idx *.ind *.ilg
	pdflatex $(DOC).tex
	bibtex $(DOC)
	pdflatex $(DOC).tex
	makeindex $(DOC)
	pdflatex $(DOC).tex
	pdflatex $(DOC).tex
	pdflatex $(DOC).tex

.PHONY: install
install: $(DOC).pdf
	$(INSTALL) -m 755 -d         $(INSTALLDIR)
	$(INSTALL) -m 644 $(DOC).pdf $(INSTALLDIR)/$(INSTALLNAME).pdf
