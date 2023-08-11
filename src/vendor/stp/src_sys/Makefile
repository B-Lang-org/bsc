PWD:=$(shell pwd)
TOP:=$(PWD)/../../../..

include $(TOP)/platform.mk

RM ?= rm -rf
CP ?= cp

LIB_DIR=../lib
INC_DIR=../include

ifeq ($(OSTYPE), Darwin)
LDFLAGS = -dynamiclib -Wl,-install_name,libstp_sys.so
else
LDFLAGS = -shared -Wl,-soname,libstp_sys.so
endif

.PHONY: all
all: install


libstp_sys.so:
	$(CP) "$(STP_LIBPATH)/libstp.so" ./libstp_sys.so

libstp.so: libstp_sys.so
	$(RM) $@
	ln -s $< $@

install: libstp_sys.so
	mkdir -p $(LIB_DIR)
	$(CP) libstp_sys.so $(LIB_DIR)/
	ln -fsn libstp.so.1 $(LIB_DIR)/libstp.so
	ln -fsn libstp_sys.so $(LIB_DIR)/libstp.so.1
	mkdir -p $(INC_DIR)
	$(CP) stp_c_interface.h $(INC_DIR)/

.PHONY: clean full_clean

clean:
	$(RM) *.o *.so

full_clean: clean
	$(RM) -R $(LIB_DIR)
	$(RM) -R $(INC_DIR)



