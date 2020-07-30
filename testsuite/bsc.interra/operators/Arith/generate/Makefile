
all:
	./gen.pl > gen_arith.v
	iverilog -DTOP=gen_arith ${BLUESPECDIR}/Verilog/main.v gen_arith.v
	./a.out > vectors 
	./sort.pl vectors > Vectors.bsv

Xclean:
	\rm -rf INCA* *.b[io] Vectors.bsv a.out gen_arith.v vectors

PWD=$(shell pwd)
CONFDIR = $(realpath ../../../..)
 
DONTKEEPFILES = Vectors.bsv a.out gen_arith.v vectors

include $(CONFDIR)/clean.mk
