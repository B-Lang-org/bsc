PWD:=$(shell pwd)
TOP:=$(PWD)/../../..

include $(TOP)/platform.mk

RM ?= rm -rf
CP ?= cp

LIB_DIR=../lib
INC_DIR=../include

ifeq ($(OSTYPE), Darwin)
LDFLAGS = -dynamiclib -Wl,-install_name,libstp_stub.so
else
LDFLAGS = -shared -Wl,-soname,libstp_stub.so
endif

.PHONY: all
all: install

stp_stub.o: stp_stub.c stp_c_interface.h
	$(CC) $(CFLAGS) -c -o $@ $<

libstp_stub.so: stp_stub.o
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

libstp.so: libstp_stub.so
	$(RM) $@
	ln -s $< $@

install: libstp_stub.so
	mkdir -p $(LIB_DIR)
	$(CP) libstp_stub.so $(LIB_DIR)/
	ln -fsn libstp.so.1 $(LIB_DIR)/libstp.so
	ln -fsn libstp_stub.so $(LIB_DIR)/libstp.so.1
	mkdir -p $(INC_DIR)
	$(CP) stp_c_interface.h $(INC_DIR)/

.PHONY: clean full_clean

clean:
	$(RM) *.o *.so

full_clean: clean
	$(RM) -R $(LIB_DIR)
	$(RM) -R $(INC_DIR)



