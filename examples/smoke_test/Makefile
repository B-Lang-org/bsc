LABNAME = Smoke Test to check Bluespec installation
SMOKENAME = FibOne

BSC=bsc -no-show-timestamps -no-show-version


## Default simulator is iverilog
VSIM = -vsim iverilog

ifdef verilator
    VSIM = -vsim verilator
endif

ifdef cvc
     VSIM = -vsim cvc
endif

ifdef vcs
    VSIM = -vsim vcs
endif

ifdef vcsi
    VSIM = -vsim vcsi
endif

ifdef ncverilog
    VSIM = -vsim ncverilog
endif

ifdef ncsim
    VSIM = -vsim ncsim
endif

ifdef modelsim
    VSIM = -vsim modelsim
endif

.PHONY: help
help:
	@echo "Smoke test to check Bluespec installation"
	@echo "  This tests that BSC can be run, to compile a basic design into"
	@echo "  both Verilog and Bluesim simulations, that run and produce the"
	@echo "  expected output."
	@echo
	@echo "  The default Verilog simulator is iverilog. To specity an alternate"
	@echo "  simulator, add one of the following to the comannad line:"
	@echo "    verilator=1, cvc=1, vcs=1, vcsi=1, ncverilog=1, ncsim=1, modelsim=1"
	@echo
	@echo "Useful targets:"
	@echo "  smoke_test         -- Run both 'smoke_test_vlog' and 'smoke_test_bsim'"
	@echo
	@echo "  smoke_test_verilog -- Run the basic test in Verilog simulation"
	@echo "  smoke_test_bluesim -- Run the basic test in Bluesim simulation"
	@echo
	@echo "  clean              --  remove intermediate files"
	@echo "  help               --  display this message"


.PRECIOUS: mk%.v

.PHONY: clean
clean:
	@rm -f *.bi *.bo *.ba 
	@rm -f *.cxx *.h *.o *.so *.bexe
	@rm -f *.v *.vexe
	@rm -f *.vcd *~ *.fsdb *.log
	@rm -f smoke_test_verilog.out smoke_test_bluesim.out
	@rm -rf csrc INCA_libs simv.daidir vfastLog/  nWaveLog/ work_mkFibOne/

## A target to check the installation of bsc
.PHONY: smoke_test
smoke_test: smoke_test_verilog smoke_test_bluesim

.PHONY:	smoke_test_verilog
smoke_test_verilog: clean
	@echo ""
	@echo "Checking Verilog generation"
	$(BSC) -verilog $(SMOKENAME).bsv
	@echo ""
	@echo "Checking Verilog simulation"
	$(BSC) $(VSIM) -e mk$(SMOKENAME) -o mk$(SMOKENAME).vexe mk$(SMOKENAME).v
	./mk$(SMOKENAME).vexe  > smoke_test_verilog.out
	@echo ""
	@echo "Comparing result of Bluespec Simulation" 
	@echo "Some simulator specific difference expected"	
	-diff mk$(SMOKENAME).out.expected smoke_test_verilog.out
	@echo ""
	@echo "Bluespec installation looks OK"

.PHONY: smoke_test_bluesim
smoke_test_bluesim: clean
	@echo ""
	@echo "Checking bsc compiles"
	$(BSC) -sim $(SMOKENAME).bsv
	@echo ""
	@echo "Checking compile for Bluespec simulator"	
	$(BSC) -sim -o mk$(SMOKENAME).bexe -e mk$(SMOKENAME) mk$(SMOKENAME).ba
	./mk$(SMOKENAME).bexe > smoke_test_bluesim.out
	@echo ""
	@echo "Comparing result of Bluespec Simulation" 
	diff mk$(SMOKENAME).out.expected smoke_test_bluesim.out
	@echo ""
	@echo "Bluespec's Bluesim looks OK"
