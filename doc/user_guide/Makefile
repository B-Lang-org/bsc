# Makefile for LaTeX-based documentation

PWD := $(shell pwd)
TOP := $(PWD)/..

PREFIX?=$(TOP)/inst

INSTALL?=install -c
RM=rm

LATEX = latex '\scrollmode\input'
PDFLATEX = pdflatex '\scrollmode\input'

# -------------------------

# Install location
INSTALLDIR=$(PREFIX)/doc

# Name in the release
INSTALLNAME=bsc_user_guide

# Local file names
DOC=user_guide

# Generated index files beyond the standard 'idx' and 'ind'
# should be named '?dx' and '?nd' (using a new unique letter)
IDX_LIST= c

## Included .tex Files
INCLUDES = \
	version.tex \
	bluetcl.tex \

# -------------------------

.PHONY: doc clean full_clean

doc:	$(DOC).pdf

clean:
	${RM} -f *.dvi *.ps *.pdf figures/*.pdf

full_clean: clean
	${RM} -f *.log *.aux *.blg *.bbl *.toc *.out *.?dx *.?nd *.ilg

$(DOC).pdf: $(DOC).tex $(INCLUDES)
	$(RM) -f *.log *.aux *.blg *.bbl *.out *.toc *.?dx *.?nd *.ilg
	-pdflatex $(DOC).tex
	-bibtex $(DOC)
	-pdflatex $(DOC).tex
	makeindex $(DOC)
	for i in $(IDX_LIST) ; do \
		makeindex $(DOC).$${i}dx -o $(DOC).$${i}nd ; \
		done
	-pdflatex $(DOC).tex
	pdflatex $(DOC).tex

.PHONY: install
install: $(DOC).pdf
	$(INSTALL) -m 755 -d         $(INSTALLDIR)
	$(INSTALL) -m 644 $(DOC).pdf $(INSTALLDIR)/$(INSTALLNAME).pdf

# -------------------------

