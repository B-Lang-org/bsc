PWD:=$(shell pwd)
TOP:=$(PWD)/../../../..

include $(TOP)/platform.mk

RM ?= rm -rf
CP ?= cp

LIB_DIR=../lib
INC_DIR=../include

ifeq ($(OSTYPE), Darwin)
LDFLAGS = -dynamiclib -Wl,-install_name,$(SNAME)
else
LDFLAGS = -shared -Wl,-soname,$(SNAME)
endif

.PHONY: all
all: install

stp_stub.o: stp_stub.c stp_c_interface.h
	$(CC) $(CFLAGS) -c -o $@ $<

$(SNAME): stp_stub.o
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $<

libstp.so: $(SNAME)
	$(RM) $@
	ln -s $< $@

install: $(SNAME)
	mkdir -p $(LIB_DIR)
	$(CP) $(SNAME) $(LIB_DIR)/
	mkdir -p $(INC_DIR)
	$(CP) stp_c_interface.h $(INC_DIR)/

.PHONY: clean full_clean

clean:
	$(RM) *.o *.so

full_clean: clean
	$(RM) -R $(LIB_DIR)
	$(RM) -R $(INC_DIR)



