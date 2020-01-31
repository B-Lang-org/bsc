.PHONY: all install clean full_clean

VERSION = v2.5.0

INSTDIRS = include include_hs lib

all: install

$(INSTDIRS):
	mkdir -p $@

install: $(INSTDIRS)
	make -C ${VERSION}

clean:
	make -C ${VERSION} clean

full_clean:
	make -C ${VERSION} full_clean
	rm -rf $(INSTDIRS)

