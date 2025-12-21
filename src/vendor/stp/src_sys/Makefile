PWD:=$(shell pwd)
TOP:=$(PWD)/../../../..

include $(TOP)/platform.mk

RM ?= rm -rf
CP ?= cp

LIB_DIR=../lib
INC_DIR=../include

.PHONY: all
all: install


$(SNAME):
	$(CP) "$(STP_LIBPATH)" ./$(SNAME)

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



