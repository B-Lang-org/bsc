# -------------------------

INSTALL_NAME = Verilog

VERI_FILES = \
	ASSIGN1.v \
	BRAM1.v \
	BRAM1Load.v \
	BRAM1BE.v \
	BRAM1BELoad.v \
	BRAM2.v \
	BRAM2Load.v \
	BRAM2BE.v \
	BRAM2BELoad.v \
	BypassCrossingWire.v \
	BypassWire.v \
	BypassWire0.v \
	ClockDiv.v \
	ClockGater.v \
	ClockGen.v \
	ClockInverter.v \
	ClockMux.v \
	ClockSelect.v \
	ConfigRegN.v \
	ConfigRegUN.v \
	ConfigRegA.v \
	ConstrainedRandom.v \
	ConvertFromZ.v \
	ConvertToZ.v \
	Counter.v \
	CRegA5.v \
	CRegN5.v \
	CRegUN5.v \
	CrossingBypassWire.v \
	CrossingRegA.v	\
	CrossingRegN.v \
	CrossingRegUN.v \
	DualPortRam.v \
	FIFO1.v \
	FIFO10.v \
	FIFO2.v \
	FIFO20.v \
	FIFOL1.v \
	FIFOL10.v \
	FIFOL2.v \
	FIFOL20.v \
	Fork.v \
	GatedClock.v \
	GatedClockDiv.v \
	GatedClockInverter.v \
	InitialReset.v \
	InoutConnect.v \
	LatchCrossingReg.v \
	MakeClock.v \
	MakeReset.v \
	MakeResetA.v \
	MakeReset0.v \
	McpRegUN.v \
	ProbeCapture.v \
	ProbeWire.v \
	ProbeHook.v \
	ProbeMux.v \
	ProbeTrigger.v \
	ProbeValue.v \
	RWire.v \
	RWire0.v \
	RegA.v	\
	RegAligned.v \
	RegFile.v \
	RegFileLoad.v \
	RegN.v \
	RegTwoA.v \
	RegTwoN.v \
	RegTwoUN.v \
	RegUN.v \
	ResetMux.v \
	ResetEither.v \
	ResetToBool.v \
	ResetInverter.v \
	ResolveZ.v \
	RevertReg.v \
	SampleReg.v \
	ScanIn.v \
	SizedFIFO.v \
	SizedFIFO0.v \
	SizedFIFOL.v \
	SizedFIFOL0.v \
	SyncBit.v \
	SyncBit15.v \
	SyncBit1.v \
	SyncBit05.v \
	SyncFIFO.v \
	SyncFIFO0.v \
	SyncFIFO1.v \
	SyncFIFO10.v \
	SyncFIFOLevel.v \
	SyncFIFOLevel0.v \
	SyncHandshake.v \
	SyncPulse.v \
	SyncRegister.v \
	SyncReset.v \
	SyncResetA.v \
	SyncReset0.v \
	SyncWire.v \
	TriState.v \
	UngatedClockMux.v \
	UngatedClockSelect.v \
	main.v \
	Empty.v \

OTHER_FILES = \
	Bluespec.xcf \

VCD_TEST_MODS = \
	SyncRegister \
	SyncFIFO \
	ClockGen \

include common.mk

# -------------------------
# some modules are duplicates of other modules

COPYMOD = $(PWD)/copy_module.pl

RegAligned.v: RegA.v
	$(COPYMOD) RegA RegAligned

ConfigRegN.v: RegN.v
	$(COPYMOD) RegN ConfigRegN

ConfigRegUN.v: RegUN.v
	$(COPYMOD) RegUN ConfigRegUN

ConfigRegA.v: RegA.v
	$(COPYMOD) RegA ConfigRegA

BypassCrossingWire.v: BypassWire.v
	$(COPYMOD) BypassWire BypassCrossingWire

# -------------------------
