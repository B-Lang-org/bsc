// Top-level driver for "verilated" objects (Verilog compiled with verilator)

#include <verilated.h>

#ifdef BSV_POSITIVE_RESET
#define BSV_RESET_VALUE 1
#else
#define BSV_RESET_VALUE 0
#endif

#ifndef BSV_RESET_NAME
#define BSV_RESET_NAME RST_N
#endif

#define Q(x) #x
#define QUOTE(x) Q(x)
#define APPEND(x,y) x ## y

#define mkV(name) APPEND(V,name)

#include QUOTE(mkV(TOP).h)

// If "verilator --trace" is used, include the tracing class
#if VM_TRACE
# include <verilated_vcd_c.h>
#endif

vluint64_t main_time = 0;    // Current simulation time

double sc_time_stamp () {    // Called by $time in Verilog
    return main_time;
}

inline void step (mkV(TOP)* TOP, VerilatedVcdC* tfp, vluint64_t incr)
{
#if VM_TRACE
    if (tfp)
      tfp->dump(main_time);
#endif
    TOP->eval ();
    main_time += incr;
}

int main (int argc, char **argv, char **env) {
    Verilated::commandArgs (argc, argv);    // remember args

    // Use a hierarchical name that matches 'main.v'
    mkV(TOP)* TOP = new mkV(TOP)("main");    // create instance of model

    VerilatedVcdC* tfp = NULL;    // pointer for tracing

#if VM_TRACE
    // If verilator was invoked with --trace argument,
    // and if at run time passed the +bscvcd argument, turn on tracing
    const char* flag = Verilated::commandArgsPlusMatch("bscvcd");
    if (flag && 0==strcmp(flag, "+bscvcd")) {
        Verilated::traceEverOn(true);  // Verilator must compute traced signals
        VL_PRINTF("Enabling waves into dump.vcd...\n");
        tfp = new VerilatedVcdC;
        TOP->trace(tfp, 99);  // Trace 99 levels of hierarchy
        tfp->open("dump.vcd");  // Open the dump file
    }
#endif

    // initial conditions
    TOP->BSV_RESET_NAME = BSV_RESET_VALUE;
    TOP->CLK = 0;
    step(TOP, tfp, 1);

    // First CLK edge to time 1
    TOP->CLK = 1;
    step(TOP, tfp, 1);

    // De-assert RST at time 2
    TOP->BSV_RESET_NAME = 1 - BSV_RESET_VALUE;
    step(TOP, tfp, 3);

    // now resume normal CLK cycle
    // negedge on 5, posedge on 10
    //
    while (! Verilated::gotFinish ()) {

	TOP->CLK = 0;
	step(TOP, tfp, 5);
	if (Verilated::gotFinish ()) break;

	TOP->CLK = 1;
	step(TOP, tfp, 5);
    }

    TOP->final ();    // Done simulating

    // Close trace if opened
#if VM_TRACE
    if (tfp) { tfp->close(); }
#endif

    delete TOP;
    TOP = NULL;

    exit (0);
}
