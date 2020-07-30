       Sample Verilog Memory Import into Bluespec SystemVerilog

These files show a simple example of importing a Verilog SRAM into
Bluespec SystemVerilog (BSV), i.e., making an existing Verilog module
that implements an SRAM available to BSV programs.

The file Verilog_SRAM_model.v is an example of a Verilog SRAM model
(the module mkVerilog_SRAM_model). Please see the comments at the top
of the file for an explanation of its ports and behavior.

The file mem_init.data is an example data file for initializing the
memory at start of simulation.  It just fills the first 32 locations
with values with a descending sequence 'h1f00, 'h1e00, ... 'h0000.

The file SRAM_wrapper.bsv shows how the Verilog model is imported into
BSV.  Please see the comments in the file for details.  Briefly:

 - The interface SRAM_ifc defines how the Verilog module should appear
   inside a BSV program, to BSV modules that use it.

 - The module mkSRAM is a "logical" module that is implemented by the
   Verilog "physical" module.  Its contents show how to connect BSV
   parameters to Verilog parameters, how to connect BSV methods to
   Verilog ports, and how the methods should be scheduled.  The
   constructs are described in Section 15 of the Bluespec
   SystemVerilog Reference Guide.

The file Test.bsv shows a small BSV testbench for this wrapped memory
module.  It instantiates the wrapped memory module, fixing the address
and data widths and providing the file name (mem_init.data) for the
initial contents of the memory.  In simulation, the testbench reads
and prints all locations (hence showing the file-initialized data),
then it overwrites all locations with particular values (address
left-shifted by 4 places), then reads and prints all locations again,
and exits.

The file Makefile shows how to build the simulation executable
(mkTop.exe), and how to run it.

The file example_output.txt shows a log of the output during simulation.

The file RAMs.bspec is a project file for use with the development workstation.

This is just an example, for illustration.  If you have a different
Verilog memory model/implementation, you should be able to modify this
example to suit your needs.
