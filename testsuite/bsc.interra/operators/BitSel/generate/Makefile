all:
	./gen.pl > gen_bits.v
	iverilog -DTOP=gen_bits ${BLUESPECDIR}/Verilog/main.v gen_bits.v
	./a.out > vectors
	./sort.pl vectors > Vectors.bsv

Xclean:
	@rm -rf INCA* *.b[io] Vectors.bsv a.out gen_bits.v vectors

	PWD=$(shell pwd)


CONFDIR = $(realpath ../../../..)

KEEPFILES = 
DONTKEEPFILES = Vectors.bsv  vectors

include $(CONFDIR)/clean.mk
