PWD:=$(shell pwd)
TOP:=$(PWD)/../..

INSTALL?= install

PREFIX?=$(TOP)/inst
INSTALLDIR=$(PREFIX)/lib/exec

.PHONY: install
install:
	$(INSTALL) -m 755 -d $(INSTALLDIR)/
	$(INSTALL) -m 755 $(TOP)/platform.sh $(INSTALLDIR)/platform.sh
	$(INSTALL) -m 755 bsc_build_vsim_vcs $(INSTALLDIR)/bsc_build_vsim_vcs
	$(INSTALL) -m 755 bsc_build_vsim_vcs $(INSTALLDIR)/bsc_build_vsim_VCS
	$(INSTALL) -m 755 bsc_build_vsim_vcsi $(INSTALLDIR)/bsc_build_vsim_vcsi
	$(INSTALL) -m 755 bsc_build_vsim_vcsi $(INSTALLDIR)/bsc_build_vsim_VCSi
	$(INSTALL) -m 755 bsc_build_vsim_vcsi $(INSTALLDIR)/bsc_build_vsim_VCSI
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_ncverilog
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_NCVerilog
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_nc
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_ncv
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_ncvlog
	$(INSTALL) -m 755 bsc_build_vsim_ncverilog $(INSTALLDIR)/bsc_build_vsim_ncsim
	$(INSTALL) -m 755 bsc_build_vsim_modelsim $(INSTALLDIR)/bsc_build_vsim_modelsim
	$(INSTALL) -m 755 bsc_build_vsim_modelsim $(INSTALLDIR)/bsc_build_vsim_Modelsim
	$(INSTALL) -m 755 bsc_build_vsim_modelsim $(INSTALLDIR)/bsc_build_vsim_ModelSim
	$(INSTALL) -m 755 bsc_build_vsim_modelsim $(INSTALLDIR)/bsc_build_vsim_questa
	$(INSTALL) -m 755 bsc_build_vsim_modelsim $(INSTALLDIR)/bsc_build_vsim_Questa
	$(INSTALL) -m 755 bsc_build_vsim_iverilog $(INSTALLDIR)/bsc_build_vsim_iverilog
	$(INSTALL) -m 755 bsc_build_vsim_iverilog $(INSTALLDIR)/bsc_build_vsim_icarus
	$(INSTALL) -m 755 bsc_build_vsim_veriwell $(INSTALLDIR)/bsc_build_vsim_veriwell
	$(INSTALL) -m 755 bsc_build_vsim_cver $(INSTALLDIR)/bsc_build_vsim_cver
	$(INSTALL) -m 755 bsc_build_vsim_cvc $(INSTALLDIR)/bsc_build_vsim_cvc
	$(INSTALL) -m 755 bsc_build_vsim_cvc $(INSTALLDIR)/bsc_build_vsim_cvc64
	$(INSTALL) -m 755 bsc_build_vsim_isim $(INSTALLDIR)/bsc_build_vsim_isim
	$(INSTALL) -m 755 bsc_build_vsim_xsim $(INSTALLDIR)/bsc_build_vsim_xsim
	$(INSTALL) -m 755 bsc_build_vsim_verilator $(INSTALLDIR)/bsc_build_vsim_verilator

.PHONY: clean full_clean
clean full_clean:
	@echo "no $@ in exec"

