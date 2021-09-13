PWD:=$(shell pwd)

TOP:=../../../..
include $(TOP)/platform.mk

REPONAME=yices2

YICES_SRC=$(REPONAME)
YICES_INST=$(abspath $(PWD)/$(REPONAME)-inst)

ifeq ($(OSTYPE), Darwin)
# On macOS we need to work around three yices build issues:
# 1. yices explicitly sets the install_name for libyices.2.dylib to be
#    the absolute install path. For cases where yices knows the correct
#    install path of the library, this makes sense, but for bsc, we don't want
#    this, as we're going to eventually install this in a separate directory
#    of our own.
# 2. libyices.2.dylib dynamically links against ligmp, which probably comes
#    from Homebrew. We don't want this, because this makes our installation
#    depend on Homebrew. Instead, statically link libgmp into libyices.
#    Note that we must statically link by using the archive file as Apple's ld
#    doesn't understand -Bstatic.
# 3. yices searches a hard-coded list of paths, which does not include
#    /opt/homebrew as used on Arm-based Macs, so we must manually pass the
#    directories to configure so it doesn't fail. Note that --with-static-gmp
#    is broken; the initial check succeeds, but it later unconditionally tries
#    an AC_CHECK_LIB(gmp, ...) and so tries to link with -lgmp, which will fail
#    if the library search path doesn't include the library, at which point
#    passing the option serves no purpose.
INCLUDEDIRGMP=$(shell pkg-config --variable=includedir gmp)
LIBDIRGMP=$(shell pkg-config --variable=libdir gmp)
CONFIGURE_ENV= \
	CPPFLAGS="$${CPPFLAGS:+$$CPPFLAGS }-I$(INCLUDEDIRGMP)" \
	LDFLAGS="$${LDFLAGS:+$$LDFLAGS }-L$(LIBDIRGMP)"
LIBGMPA=$(LIBDIRGMP)/libgmp.a
BUILD_ARGS=libyices_install_name=libyices.2.dylib LIBS=$(LIBGMPA)
endif

.PHONY: all
all: install

.PHONY: install
install:
ifeq ($(YICES_STUB),)
	(cd $(YICES_SRC) ; \
		autoconf ; \
		$(CONFIGURE_ENV) ./configure --prefix=$(YICES_INST) ; \
		$(MAKE) $(BUILD_ARGS); \
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
