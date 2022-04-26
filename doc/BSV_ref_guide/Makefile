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
INSTALLNAME=bsc_libraries_ref_guide

# Local file names
DOC=BSV_lang

## Included .tex Files
INCLUDES = \
	version.tex \
	keywords.tex \

# -------------------------

.PHONY: doc clean full_clean

doc:	$(DOC).pdf

clean:
	${RM} -f *.dvi *.ps *.pdf extractGrammar \
		temp.tex  non_terminals.txt  keywords.tex rawbnf.tex

full_clean: clean
	${RM} -f *.log *.aux *.blg *.bbl *.toc *.out *.?dx *.?nd *.ilg

# ----------------------------------------------------------------
# Program to automatically extract grammar productions and keywords
# from LaTeX source

extractGrammar: extractGrammar.c
	cc -Wall extractGrammar.c -o extractGrammar

# Automatically extract grammar productions and keyword-list
#i.e. rawbnf.tex non_terminals.tex and keywords.tex

keywords.tex: $(DOC).tex  extractGrammar
	./extractGrammar  $(DOC).tex 
	cp -f keywords.tex temp.tex
	sed -es/\\\\_/_/g temp.tex > keywords.tex 

# ----------------------------------------------------------------
# Warning: .pdf rule does not have dependencies on Figures/*

$(DOC).pdf: $(DOC).tex $(INCLUDES)
	$(RM) -f *.log *.aux *.blg *.bbl *.out *.toc *.?dx *.?nd *.ilg
	-pdflatex $(DOC).tex
	-bibtex $(DOC)
	-pdflatex $(DOC).tex
	makeindex $(DOC)
	-pdflatex $(DOC).tex
	pdflatex $(DOC).tex

.PHONY: install
install: $(DOC).pdf
	$(INSTALL) -m 755 -d         $(INSTALLDIR)
	$(INSTALL) -m 644 $(DOC).pdf $(INSTALLDIR)/$(INSTALLNAME).pdf

# -------------------------
