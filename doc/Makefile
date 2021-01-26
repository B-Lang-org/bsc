PWD := $(shell pwd)
TOP := $(PWD)/..

PREFIX?=$(TOP)/inst

SUBDIRS=\
	user_guide \
	libraries_ref_guide \

.PHONY: all
all: install

.PHONY: install clean full_clean
install clean full_clean:
	for d in $(SUBDIRS) ; do \
		$(MAKE)  -C $$d  PREFIX=$(PREFIX)  $@ ; \
		done
