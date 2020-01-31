PWD:=$(shell pwd)
TOP:=$(PWD)/../../..

# Requires that TOP be set
# Sets BUILDDIR, and BSC and BSCFLAGS if not set
include ../common.mk

SRCS = $(wildcard *.bs) $(wildcard *.bsv)

# Only .bo files are generated (no modules are elaborated in this directory)
OBJS = $(addprefix $(BUILDDIR)/,$(addsuffix .bo,$(basename $(SRCS))))

.PHONY: build
build: $(BUILDDIR) $(OBJS)

$(BUILDDIR):
	mkdir -p $@

# .bs.bo:
$(BUILDDIR)/%.bo: %.bs
	${BSC} ${BSCFLAGS} $<

# .bsv.bo:
$(BUILDDIR)/%.bo: %.bsv
	${BSC} ${BSCFLAGS} $<

.PHONY: clean full_clean
clean full_clean:
	@rm -f *.bi *.bo *.ba vpi_wrapper* *.info *~

# remake the dependency file, requires bluetcl and more to boot strap
.PHONY: depends
depends:
	bluetcl -exec makedepend -bdir "$(BUILDDIR)" "$(SRCS)" | sed -e 's|$(BUILDDIR)|$$(BUILDDIR)|g' > depends.mk

sinclude depends.mk
