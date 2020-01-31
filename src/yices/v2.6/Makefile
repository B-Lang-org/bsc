PWD:=$(shell pwd)

REPONAME=yices2

YICES_SRC=$(REPONAME)
YICES_INST=$(abspath $(PWD)/$(REPONAME)-inst)


.PHONY: all
all: install

.PHONY: install
install:
	(cd $(YICES_SRC) ; \
		autoconf ; \
		./configure --prefix=$(YICES_INST) ; \
		make ; \
		make install \
		)
	ln -fsT $(YICES_INST)/include include
	ln -fsT $(YICES_INST)/lib lib
	ln -fsT HaskellIfc include_hs

.PHONY: clean
clean:
	make -C $(YICES_SRC) all-clean

.PHONY: full_clean
full_clean: clean
	rm -f include_hs
	rm -rf $(YICES_INST)
	rm -f include lib
