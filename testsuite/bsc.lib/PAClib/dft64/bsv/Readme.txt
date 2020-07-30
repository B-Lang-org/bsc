---------------------------------------------------------------------
-- 27 Sept 2010 --
The package provide another version of a DFT module, which takes
advantage of some of the feature in the PAClib library.

File:
DFT_v0.bsv, Tb_v0.bsv DFT_v0.bspec
  These files have been renamed by adding the _v0 suffix.  The code
  remains more or less unchanged.

DFT.bsv
  This file contains common code used between the DFT_v0 and DFT_v1
  examples.

DFT_v1.bsv
  Implementation of DFT using PAClib library.  A picture is needed
  here.

Tb_v1.bsv
  Test bench for DFT_v1.bsv.

PAClib.bsv
  A modified version of PAClib, The module mkReplicateFn has been
  added.  Some unnecessary provisos have been removed.

DFT_v1.bspec
  Project file for version 1.

---------------------------------------------------------------------
--  24 Sept 2010 ---
This tar file contains a first pass at a DFT module.  Most of the code
is focused on building test bench and related to verify the DFT
module.  In this version, the DFT module is fully parallel,  all
multiplication and additions occur in 1 cycle.  Clearly this is not a
synthesizable module, but rather one to verify the algorithm.

There is a Bluespec project file, which can be open with
bluespec DFT.bspec


The test bench works by reading a set of point from a file (Test.dat)
applying the DFT and writing out the result (Test.datout).  The
repeats for up to 10 data sets as specified in Tb.bsv

Next steps for this are further testing and design of an hardware
efficient DFT architecture.


File: (bottom up listing)
Utils.bsv:
  This Bluespec package provide some additional Complex and FixedPoint
  functions, specifically those needed to multiple and truncate
  Complex FixedPoint numbers of unequal sizes.

FixedPointIO.bsv  FixedPointIO.c
  These files are used to provided utility functions to read and write
  FixedPoint Data to the file system during run-time.  The C functions
  are wrapped in the import BDPI mechanism, to provide the low-level
  IO and missing in Verilog.

DFTCoef.bsv
  This file contains a Vector of 128 Real numbers which provide the
  coefficients for the DFT.  The Vector of Reals are converted to a
  Vector of Complex or Reals in this file.   In the core DFT code, the
  Reals are converted to the FixedPoint data of the desired sized
  during static elaboration.

DFT.bsv
  This is the core of the DFT models.   In this file the appropriate
  configuration, data types and modules are defined.  The core DFT
  processing module has a server interface which takes a Vector of
  Complex and return the DFT for that set.  The amount of HW and hence
  the latency is controlled by the configuration parameters.
  in the file for specific details.

Tb.bsv
  This contains a simple test bench which reads data from a file
  applies the DFT and writes output to another file.

DFT.bspec
  A Bluespec project file.
