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

// Tracing: verilator compiles in exactly one format -- VCD (--trace) or FST
// (--trace-fst), which are mutually exclusive and signalled by VM_TRACE_FST.
// Select the matching writer class and the plusarg/filename for it.  With
// -dump-formats none (no --trace) VM_TRACE is 0 and nothing below is compiled.
#if VM_TRACE
# if defined(VM_TRACE_FST) && VM_TRACE_FST
#  include <verilated_fst_c.h>
typedef VerilatedFstC BscTraceC;
#  define BSC_DUMP_FILE "dump.fst"
#  define BSC_DUMP_ARG  "bscfst"
#  define BSC_OTHER_ARG "bscvcd"
# else
#  include <verilated_vcd_c.h>
typedef VerilatedVcdC BscTraceC;
#  define BSC_DUMP_FILE "dump.vcd"
#  define BSC_DUMP_ARG  "bscvcd"
#  define BSC_OTHER_ARG "bscfst"
# endif
static BscTraceC* tfp = NULL;    // harness trace file (guarded by VM_TRACE)
#endif

vluint64_t main_time = 0;    // Current simulation time

double sc_time_stamp () {    // Called by $time in Verilog
    return main_time;
}

inline void step (mkV(TOP)* TOP, vluint64_t incr)
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

#if VM_TRACE
    // +bscvcd / +bscfst: open the harness dump in whichever format this binary
    // was built for (BSC_DUMP_ARG).  The format is fixed at build time
    // (--trace vs --trace-fst), so passing the *other* format's plusarg errors.
    const char* flag = Verilated::commandArgsPlusMatch(BSC_DUMP_ARG);
    if (flag && 0==strcmp(flag, "+" BSC_DUMP_ARG)) {
        Verilated::traceEverOn(true);  // Verilator must compute traced signals
        VL_PRINTF("Enabling waves into %s...\n", BSC_DUMP_FILE);
        tfp = new BscTraceC;
        TOP->trace(tfp, 99);  // Trace 99 levels of hierarchy
        tfp->open(BSC_DUMP_FILE);  // Open the dump file
    }
    const char* other = Verilated::commandArgsPlusMatch(BSC_OTHER_ARG);
    if (other && 0==strcmp(other, "+" BSC_OTHER_ARG)) {
        VL_PRINTF("%%Error: this model was built for %s, not +%s "
                  "(rebuild with a different -dump-formats)\n",
                  BSC_DUMP_FILE, BSC_OTHER_ARG);
    }
#else
    // Built with -dump-formats none (no --trace): no dumping is compiled in.
    // Fail loudly if a dump was requested rather than silently doing nothing.
    const char* nov = Verilated::commandArgsPlusMatch("bscvcd");
    const char* nof = Verilated::commandArgsPlusMatch("bscfst");
    if ((nov && 0==strcmp(nov, "+bscvcd")) || (nof && 0==strcmp(nof, "+bscfst"))) {
        VL_PRINTF("%%Error: this model was built with -dump-formats none; "
                  "no waveform dumping is available\n");
    }
#endif

    // initial conditions
    TOP->BSV_RESET_NAME = BSV_RESET_VALUE;
    TOP->CLK = 0;
    step(TOP, 1);

    // First CLK edge to time 1
    TOP->CLK = 1;
    step(TOP, 1);

    // De-assert RST at time 2
    TOP->BSV_RESET_NAME = 1 - BSV_RESET_VALUE;
    step(TOP, 3);

    // now resume normal CLK cycle
    // negedge on 5, posedge on 10
    //
    while (! Verilated::gotFinish ()) {

	TOP->CLK = 0;
	step(TOP,5);
	if (Verilated::gotFinish ()) break;

	TOP->CLK = 1;
	step(TOP,5);
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
