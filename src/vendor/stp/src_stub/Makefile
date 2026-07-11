PWD:=$(shell pwd)
TOP:=$(PWD)/../../../..

include $(TOP)/platform.mk

RM ?= rm -rf
CP ?= cp

LIB_DIR=../lib
INC_DIR=../include

ifeq ($(OSTYPE), Darwin)
SNAME = libstp.dylib
LDFLAGS = -dynamiclib -Wl,-install_name,$(SNAME)
LINKCMD = :
else
SNAME = libstp.so.1
LDFLAGS = -shared -Wl,-soname,$(SNAME)
LINKCMD = ln -fsn $(SNAME) $(LIB_DIR)/libstp.so
endif

.PHONY: all
all: install

stp_stub.o: stp_stub.c stp_c_interface.h
	$(CC) $(CFLAGS) -c -o $@ $<

$(SNAME): stp_stub.o
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

install: $(SNAME)
	mkdir -p $(LIB_DIR)
	$(CP) $(SNAME) $(LIB_DIR)/
	$(LINKCMD)
	mkdir -p $(INC_DIR)
	$(CP) stp_c_interface.h $(INC_DIR)/

.PHONY: clean full_clean

clean:
	$(RM) *.o *.so *.dylib

full_clean: clean
	$(RM) -R $(LIB_DIR)
	$(RM) -R $(INC_DIR)



