#ifndef __KERNEL_H__
#define __KERNEL_H__

#include <deque>

#include "bluesim_kernel_api.h"
#include "bs_model.h"
#include "bs_vcd.h"
#include "event_queue.h"
#include "portability.h"


/*
 * VCD state
 */

/* state */

typedef enum { VCD_OFF, VCD_HEADER, VCD_ENABLED, VCD_DISABLED } tVCDStatus;

// Represents a change of a value
class Change
{
public:
  // Change to X
  Change(unsigned int n, unsigned int b)
    : num(n), bits(b), isX(true)
  {}
  // Change to a new value (<= 64 bits)
  Change(unsigned int n, unsigned int b, tUInt64 v)
    : num(n), bits(b), isX(false), narrow(v)
  {}
  // Change to a new value (> 64 bits)
  Change(unsigned int n, const tUWide& v)
    : num(n), bits(v.size()), isX(false), wide(v)
  {}
public:
  tUInt32 num;   // VCD ID number
  unsigned int bits;  // bit width
  bool isX;           // is an X value
  tUInt64 narrow;     // narrow data
  tUWide  wide;       // wide data
};

// Represents the list of changes at a single time
typedef std::list<Change> tChangeList;

typedef std::multimap<unsigned int, tClock> tClockMap;

struct tVCDState {
  tVCDStatus state;
  tUInt64 vcd_filesize_limit;
  bool go_xs;
  tUInt32 next_seq_num;
  tUInt32 kept_seq_num;
  bool is_backing_instance;

  std::string vcd_file_name;
  std::set<std::string> previous_files;

  tClockMap clk_map;                    // clks for each VCD num

  std::map<tTime,tChangeList> changes;  // all pending changes
  std::map<tTime,const char*> tasks;    // all pending VCD tasks
  tTime min_pending;                    // lowest time of pending events
  tTime last_time_written;              // last time values were written
  bool need_end_task;                   // if we are within a $* task
  bool changes_now;                     // treat changes as immediate

  // external interface
  FILE* vcd_file;
  bool vcd_enabled;
  bool vcd_checkpoint;
  tUInt32 vcd_depth;

  char* vcd_timescale;
};

typedef struct tVCDState tVCDState;

/* A tLabel provides the information for creating a label when
 * dumping rule firing information.
 */
typedef struct {
  unsigned int indent;
  const char*  text;
} tLabel;

/* A tClockInfo is a complete description a clock waveform
 * and the schedules which execute on its edges.
 */
typedef struct
{
  char* name;                       /* clock name */
  tClockValue current_value;        /* current clock value */
  tClockValue initial_value;        /* initial clock value */
  bool has_initial_value;           /* whether the initial value is set */
  tTime initial_delay;              /* when is the first edge */
  tTime low_phase_length;           /* duration of low clock phase */
  tTime high_phase_length;          /* duration of high clock phase */
  tTime period;                     /* clock period (sum of low + high) */
  tTime negedge_at;                 /* time of last negedge */
  tTime posedge_at;                 /* time of last posedge */
  tTime combinational_at;           /* time of last combinational update */
  tScheduleFn on_posedge;           /* posedge schedule function */
  tScheduleFn after_posedge;        /* post-posedge schedule function */
  tScheduleFn on_negedge;           /* negedge schedule function */
  tScheduleFn after_negedge;        /* post-negedge schedule function */
  tUInt64 posedge_count;            /* count of number of posedges */
  tUInt64 negedge_count;            /* count of number of negedges */
  tUInt64 posedge_limit;            /* call UI on posedge count */
  tUInt64 negedge_limit;            /* call UI on negedge count */
  unsigned int vcd_num;             /* Seq. # for VCD dumping */
} tClockInfo;

/*
 * Simulation kernel state
 */
struct tSimState {
  // handle to the design
  Model* model;

  // current simulation time
  tTime sim_time;
  // scaling factor used for $time/$stime and vcds
  tTime sim_timescale;

  // a priority queue of locally-defined clock edges
  EventQueue* queue;

  // semaphores, etc. used for synchronization between API and sim_thread
  volatile bool sim_running;
  volatile bool sim_shutting_down;
  tSemaphore* start_semaphore; /* used to trigger simulation start */
  tSemaphore* stop_semaphore;  /* used to indicate simulation stop */
  pthread_mutex_t sim_mutex;   /* used to protect sim_running, etc. */
  pthread_t sim_thread_id;

  // flag to record when executing a combinational logic schedule
  bool in_combo_schedule;

  // flags marking when $stop or $finish has been executed
  bool stop_called;
  bool finish_called;
  bool abort_called;
  tSInt32 exit_status;
  volatile bool force_halt;

  // flag that records current state dump setting
  bool  call_dump_state;
  tTime last_state_dump_time;

  // flag that records current cycle dump setting
  bool call_dump_cycle_counts;

  // an array of all clock definitions
  std::vector<tClockInfo> clocks;

  // a symbol for the top module
  tSym top_symbol;

  // the current dummy edge status
  unsigned int need_dummy_edges;

  // for managing event callbacks
  tTime target_yield_time;
  unsigned int data_to_match;

  // for dumping rule firings
  std::deque<tLabel> labels;
  unsigned int rule_name_indent;

  // simulator arguments
  std::vector<const char*> plus_args;

  // Count the number of primitives that have requested reset ticks
  unsigned int reset_tick_requests;

  // VCD state
  tVCDState vcd;

};

typedef struct tSimState tSimState;

#endif /* __KERNEL_H__ */
