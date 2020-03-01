PWD:=$(shell pwd)

REPONAME=yices2

YICES_SRC=$(REPONAME)
YICES_INST=$(abspath $(PWD)/$(REPONAME)-inst)


.PHONY: all
all: install

.PHONY: install
install:
ifeq ($(YICES_STUB),)
	(cd $(YICES_SRC) ; \
		autoconf ; \
		./configure --prefix=$(YICES_INST) ; \
		$(MAKE); \
		$(MAKE) install \
		)
else
	(cd stub ; make install)
endif
	ln -fsn $(YICES_INST)/include
	ln -fsn $(YICES_INST)/lib
	ln -fsn HaskellIfc include_hs

.PHONY: clean
clean:
ifeq ($(YICES_STUB),)
	$(MAKE) -C $(YICES_SRC) all-clean
else
	$(MAKE) -C stub full_clean
endif

.PHONY: full_clean
full_clean: clean
	rm -f include_hs
	rm -rf $(YICES_INST)
	rm -f include lib
