.PHONY: all install clean full_clean

VERSION = v2.5.0

INSTDIRS = include include_hs lib

all: install

$(INSTDIRS):
	mkdir -p $@

install: $(INSTDIRS)
	$(MAKE) -C ${VERSION}

clean:
	$(MAKE) -C ${VERSION} clean

full_clean:
	$(MAKE) -C ${VERSION} full_clean
	rm -rf $(INSTDIRS)

