all:
	./gen.pl > gen_logic.v
	iverilog -DTOP=gen_logical ${BLUESPECDIR}/Verilog/main.v gen_logic.v
	./a.out > vectors 
	./sort.pl vectors > Vectors.bsv

Xclean:
	\rm -rf *.log INCA* *.b[io] Vectors.bsv a.out vectors

		PWD=$(shell pwd)



CONFDIR = $(realpath ../../../..)

KEEPFILES = 
DONTKEEPFILES = Vectors.bsv vectors 

include $(CONFDIR)/clean.mk
