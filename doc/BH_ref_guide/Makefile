AWK=awk
RM=rm
INSTALL?=install -c

PAPERSIZE=letter

DOC=BH_lang
LIBS=	Prelude.tex List.tex ListN.tex Monad.tex Environment.tex \
	Assert.tex Reserved.tex Enum.tex Tabulate.tex UIntRange.tex \
	EqFunction.tex Once.tex Push.tex Pull.tex Boolify.tex \
	OInt.tex ActionSeq.tex \
	Wallace.tex PopCount.tex BitonicSort.tex LFSR.tex  \
	Connectable.tex GetPut.tex ClientServer.tex CGetPut.tex \
	RAM.tex TRAM.tex SyncSRAM.tex SRAM.tex STRAM.tex SPSRAM.tex DPSRAM.tex \
	ClockConv.tex CompletionBuffer.tex  \
	SRAMFile.tex BGetPut.tex IVec.tex FIFO.tex FIFOF.tex ConfigReg.tex \
	ListReg.tex ListFIFO.tex RPush.tex RWire.tex Fork.tex

PWD:=$(shell pwd)

# Assume that 'bsc' is checked out as a sibling of 'bsc-doc'
# BSCDIR=$(PWD)/../../../bsc

# BSSRC=$(BSCDIR)/src/comp
# PREL=$(BSCDIR)/src/lib/Prelude
# LIBR=$(BSCDIR)/src/lib/Libraries
# OBSEL=$(BSCDIR)/src/lib/Obsolete

# BSSRC=$(BSCDIR)/src/comp

PREL=lib/Prelude
LIBR=lib/Libraries
OBSEL=lib/Obsolete

PWD := $(shell pwd)
TOP := $(PWD)/../..

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/doc
INSTALLNAME=BH_lang_ref_guide

VPATH=${PREL} ${LIBR} ${OBSEL}

.PATH:	${VPATH}

all:	$(DOC).pdf

clean:
	${RM} -f ${LIBS} *.pdf  *.blg *.bbl *.aux *.log *.toc *.idx *.ind *.ilg *.out

full_clean: clean
	${RM} -f *.log *.aux *.blg *.bbl *.out *.toc *.idx *.ind *.ilg
	${RM} -f ${LIBS}

$(DOC).pdf: $(DOC).tex  version.tex
	$(RM) -f *.log *.aux *.blg *.bbl *.out *.toc *.idx *.ind *.ilg
	pdflatex $(DOC).tex
	bibtex $(DOC)
	pdflatex $(DOC).tex
	makeindex $(DOC)
	pdflatex $(DOC).tex
	pdflatex $(DOC).tex
	pdflatex $(DOC).tex

print:	$(DOC).ps
	lpr $(DOC).ps

.PHONY: install
install: $(DOC).pdf
	$(INSTALL) -m 755 -d         $(INSTALLDIR)
	$(INSTALL) -m 644 $(DOC).pdf $(INSTALLDIR)/$(INSTALLNAME).pdf
