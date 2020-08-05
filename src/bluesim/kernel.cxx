#include <list>
#include <algorithm>
#include <cstring>
#include <cstdio>

#include <pthread.h>
#include <signal.h>

#include "mem_alloc.h"
#include "kernel.h"
#include "bs_module.h"
#include "plusargs.h"
#include "version.h"
#include "portability.h"


/* forward declarations of some static helper functions */
static void setup_state_dump_events(tSimStateHdl simHdl, bool initial);
static void setup_vcd_events(tSimStateHdl simHdl);
static void setup_clock_edges(tSimStateHdl simHdl, tClock clk);

/* mutex operations */

static void lock_sim_state(tSimStateHdl simHdl)
{
  if (pthread_mutex_lock(&(simHdl->sim_mutex)) != 0)
    perror("lock_sim_state()");
}

static void unlock_sim_state(tSimStateHdl simHdl)
{
  if (pthread_mutex_unlock(&(simHdl->sim_mutex)) != 0)
    perror("unlock_sim_state()");
}

/* Stop the simulation thread until told to restart */
static void pause_sim(tSimStateHdl simHdl)
{
  fflush(NULL); /* flush open file buffers */

  /* The stop_semaphore is used to indicate when simulation
   * stops.  It is posted here and can be waited on in
   * wait_for_sim_stop().
   */
  post_semaphore(simHdl->stop_semaphore);

  /* The start_semaphore is used to control simulation wake-up.
   * It is waited on here and posted in bk_advance, so that
   * we know the simulation will wake-up exactly once for
   * each call to bk_advance().
   */
  wait_on_semaphore(simHdl->start_semaphore);
}

/* Wait for the simulation thread to stop in pause_sim().
 * This is a hard-wait and should only be called when we know
 * the simulation thread is actually running (or going to run).
 */
static void wait_for_sim_stop(tSimStateHdl simHdl)
{
  /* Wait for the simulation thread to stop */
  wait_on_semaphore(simHdl->stop_semaphore);

  fflush(NULL); /* flush open file buffers */
}

/*
 * SIGINT handler which triggers a simulation stop via bk_abort_now()
 */

// list of sims that have registered their interest in the signal
// (use a list, so that iterators are still valid after an erase)
static std::list<tSimStateHdl> abort_watchers;

static void abort_handler(int /* unused */)
{
  std::list<tSimStateHdl>::iterator it;
  for (it = abort_watchers.begin(); it != abort_watchers.end(); it++)
    bk_abort_now(*it);
}

static void add_abort_watcher(tSimStateHdl simHdl)
{
  abort_watchers.push_back(simHdl);
}

static void remove_abort_watcher(tSimStateHdl simHdl)
{
  std::list<tSimStateHdl>::iterator it;
  // list iterators are valid after an erase, except for the erased iterator;
  // therefore, a for-loop is OK, but do the increment before erasing
  for (it = abort_watchers.begin(); it != abort_watchers.end(); ) {
    if ((*it) == simHdl) {
      std::list<tSimStateHdl>::iterator next_it = it;
      next_it++;
      abort_watchers.erase(it);
      it = next_it;
    } else {
      it++;
    }
  }
}

/*
 * Simulation thread which handles the actual simulation event queue
 * operations.  It communicates with the rest of the API through
 * semaphore operations in pause_sim, bk_advance and wait_for_sim_stop.
 */
static void* sim_thread(void* ptr)
{
  tSimState* simHdl = (tSimState*)ptr;

  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return NULL;

  /* install signal handlers to shut down simulation */
  struct sigaction sa;
  sa.sa_flags = 0;
  sa.sa_handler = abort_handler;
  sigemptyset(&sa.sa_mask);
  /* SIGINT (user types Ctrl-C) */
  sigaction(SIGINT, &sa, NULL);
  /* SIGPIPE (usually stdout piped to a program that exits, eg /usr/bin/head) */
  sigaction(SIGPIPE, &sa, NULL);

  /* add this sim to the signal watch list */
  add_abort_watcher(simHdl);

  while (!simHdl->sim_shutting_down)
  {
    /* yield to the UI and wait for a trigger to execute */
    lock_sim_state(simHdl);
    simHdl->sim_running = false;
    unlock_sim_state(simHdl);
    pause_sim(simHdl);

    /* execute the events in the simulation queue */
    simHdl->force_halt = false;
    while (bk_is_running(simHdl) && !simHdl->sim_shutting_down)
      simHdl->queue->execute(simHdl);
  }

  /* remove this sim from the signal watch list */
  remove_abort_watcher(simHdl);

  pthread_exit(NULL);
}

/*
 * Functions to abstract the implementation of the event data
 * for clock events.
 */

tClock get_clock_event_clk(unsigned int value)
{
  return ((tClock) (value >> 1));
}

tEdgeDirection get_clock_event_dir(unsigned int value)
{
  return ((tEdgeDirection) (value & 1));
}

unsigned int set_clock_event_data(tClock clk, tEdgeDirection dir)
{
  if (dir == POSEDGE)
    return ( (clk << 1) | 1 );
  else
    return ( (clk << 1)     );
}

/*
 * Event callbacks which are used to trigger execution
 * of kernel features.
 */

static tTime reset_model_event(tSimStateHdl simHdl, tEvent& ev)
{
  simHdl->model->reset_model(ev.data.flag);
  return 0llu; // not a recurring event
}

static tTime dump_state_event(tSimStateHdl simHdl, tEvent& ev)
{
  bool initial = ev.data.flag;

  if (initial)
    bk_dump_state(simHdl, "Initial State");
  else
    bk_dump_state(simHdl, "State");

  return 0llu;
}

static void print_cycle_description(tSimStateHdl simHdl,
				    tClock clk,
                                    tEdgeDirection dir,
                                    tTime time,
                                    bool combo = false)
{
  const char* clock_name = simHdl->clocks[clk].name;

  tUInt64 cycle_count;
  if (dir == POSEDGE)
    cycle_count = simHdl->clocks[clk].posedge_count + 1;
  else
    cycle_count = simHdl->clocks[clk].negedge_count + 1;
  const char* combo_str = combo ? "after-" : "";
  char dir_char = (dir == POSEDGE) ? '/' : '\\';
  printf("%s%c%s @ %llu (cycle %llu)\n",
         combo_str, dir_char, clock_name, time, cycle_count);
}

static tTime dump_cycle_event(tSimStateHdl simHdl, tEvent& ev)
{
  unsigned int n = ev.data.value;
  tClock         clk = get_clock_event_clk(n);
  tEdgeDirection dir = get_clock_event_dir(n);

  if (clk == BAD_CLOCK_HANDLE)
    return 0llu;

  print_cycle_description(simHdl, clk, dir, ev.at);

  // don't reschedule initial cycle descriptions
  if (priority_group(ev.priority) != PG_INITIAL)
    return simHdl->clocks[clk].period;
  else
    return 0llu;
}

static tTime run_edge_schedule_event(tSimStateHdl simHdl, tEvent& ev)
{
  unsigned int n = ev.data.value;
  tClock         clk = get_clock_event_clk(n);
  tEdgeDirection dir = get_clock_event_dir(n);
  bool need_to_yield = false;

  // update time
  simHdl->sim_time = ev.at;

  // update the clock edge information
  tScheduleFn schedule;
  if (dir == POSEDGE)
  {
    schedule = simHdl->clocks[clk].on_posedge;

    // if necessary, dump the cycle count for an aperiodic clock here
    if (simHdl->call_dump_cycle_counts && schedule &&
        (simHdl->clocks[clk].low_phase_length == 0) &&
        (simHdl->clocks[clk].high_phase_length == 0))
    {
      print_cycle_description(simHdl, clk, POSEDGE, simHdl->sim_time);
    }

    simHdl->clocks[clk].current_value = CLK_HIGH;
    simHdl->clocks[clk].combinational_at = simHdl->clocks[clk].posedge_at;
    simHdl->clocks[clk].posedge_at = simHdl->sim_time;
    simHdl->clocks[clk].posedge_count += 1llu;
    need_to_yield |=
      (simHdl->clocks[clk].posedge_count == simHdl->clocks[clk].posedge_limit);
  }
  else
  {
    schedule = simHdl->clocks[clk].on_negedge;

    // if necessary, dump the cycle count for an aperiodic clock here
    if (simHdl->call_dump_cycle_counts && schedule &&
        (simHdl->clocks[clk].low_phase_length == 0) &&
        (simHdl->clocks[clk].high_phase_length == 0))
    {
      print_cycle_description(simHdl, clk, NEGEDGE, simHdl->sim_time);
    }

    simHdl->clocks[clk].current_value = CLK_LOW;
    simHdl->clocks[clk].combinational_at = simHdl->clocks[clk].negedge_at;
    simHdl->clocks[clk].negedge_at = simHdl->sim_time;
    simHdl->clocks[clk].negedge_count += 1llu;
    need_to_yield |=
      (simHdl->clocks[clk].negedge_count == simHdl->clocks[clk].negedge_limit);
  }

  // reset the stop/abort flags
  simHdl->stop_called = false;
  simHdl->abort_called = false;

  // run the schedule function
  if (schedule)
  {
    schedule(simHdl, simHdl->model->get_instance());

    // if necessary, schedule the state dumping event
    if (simHdl->call_dump_state)
      setup_state_dump_events(simHdl, false);
  }

  // if necessary, schedule the VCD dumping event
  if (vcd_is_active(simHdl))
    setup_vcd_events(simHdl);

  // if necessary, setup to yield to the UI at the end of this timeslice
  if (need_to_yield || simHdl->force_halt)
  {
    simHdl->force_halt = false;
    bk_schedule_ui_event(simHdl, simHdl->sim_time);
  }

  // don't repeat initial events
  if (priority_group(ev.priority) != PG_INITIAL)
    return simHdl->clocks[clk].period;
  else
    return 0llu;
}

static tTime run_combo_schedule_event(tSimStateHdl simHdl, tEvent& ev)
{
  unsigned int n = ev.data.value;
  tClock         clk = get_clock_event_clk(n);
  tEdgeDirection dir = get_clock_event_dir(n);

  tScheduleFn schedule;
  if (dir == POSEDGE)
    schedule = simHdl->clocks[clk].after_posedge;
  else
    schedule = simHdl->clocks[clk].after_negedge;

  if (schedule) {
    simHdl->in_combo_schedule = true;
    schedule(simHdl, simHdl->model->get_instance());
    simHdl->in_combo_schedule = false;
  }

  return simHdl->clocks[clk].period;
}

static tTime vcd_event(tSimStateHdl simHdl, tEvent& ev)
{
  // if writing a new header, dump the hierarchy and id map
  if (vcd_write_header(simHdl))
  {
    vcd_write_scope_start(simHdl, "main");
    simHdl->model->dump_VCD_defs();
    vcd_write_scope_end(simHdl);
    fputs("$enddefinitions $end\n", (simHdl->vcd).vcd_file);
  }

  vcd_advance(simHdl, ev.data.flag);

  tVCDDumpType dt = get_VCD_dump_type(simHdl);
  switch (dt)
  {
    case VCD_DUMP_XS:
    {
      vcd_task(simHdl, "$dumpoff");
      for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
        vcd_write_x(simHdl, simHdl->clocks[clk].vcd_num, 1);
      simHdl->model->dump_VCD(dt);
      break;
    }
    case VCD_DUMP_INITIAL:
    {
      vcd_task(simHdl, "$dumpvars");
      for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
      {
        if ( simHdl->clocks[clk].has_initial_value ||
             (bk_clock_cycle_count(simHdl, clk) != 0llu) )
          vcd_write_val(simHdl, simHdl->clocks[clk].vcd_num,
			bk_clock_val(simHdl, clk), 1);
      }
      simHdl->model->dump_VCD(dt);
      break;
    }
    case VCD_DUMP_CHECKPOINT:
    {
      vcd_task(simHdl, "$dumpall");
      for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
        vcd_write_val(simHdl, simHdl->clocks[clk].vcd_num,
		      bk_clock_val(simHdl, clk), 1);
      simHdl->model->dump_VCD(dt);
      break;
    }
    case VCD_DUMP_CHANGES:
    {
      tTime now = bk_now(simHdl);
      for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
      {
        if ((simHdl->clocks[clk].posedge_at == now) ||
	    (simHdl->clocks[clk].negedge_at == now))
          vcd_write_val(simHdl, simHdl->clocks[clk].vcd_num,
			bk_clock_val(simHdl, clk), 1);
      }
      simHdl->model->dump_VCD(dt);
      break;
    }
    case VCD_DUMP_RESTART:
    {
      vcd_task(simHdl, "$dumpon");
      for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
        vcd_write_val(simHdl, simHdl->clocks[clk].vcd_num,
		      bk_clock_val(simHdl, clk), 1);
      simHdl->model->dump_VCD(dt);
      break;
    }
    default: break;
  }

  vcd_check_file_size(simHdl);

  return 0llu;
}

static tTime quit_event(tSimStateHdl simHdl, tEvent& /* unused */)
{
  simHdl->queue->clear();
  return 0llu;
}

static tTime yield_event(tSimStateHdl simHdl, tEvent& ev)
{
  lock_sim_state(simHdl);
  simHdl->sim_running = false;
  simHdl->sim_time = ev.at;
  unlock_sim_state(simHdl);
  pause_sim(simHdl);
  if (simHdl->sim_shutting_down)
    simHdl->queue->clear();
  return (0llu);
}

/*
 * Utility routines used to manage event callbacks.
 */

static bool isMatchingYieldEvent(tSimStateHdl simHdl, const tEvent& ev)
{
  return ((ev.fn == yield_event) &&
          (ev.at == simHdl->target_yield_time) &&
          (ev.priority == make_priority(PG_FINAL, PS_UI)));
}

static bool isMatchingScheduleEvent(tSimStateHdl simHdl, const tEvent& ev)
{
  return ((ev.fn == run_edge_schedule_event ||
           ev.fn == run_combo_schedule_event) &&
          ev.data.value == simHdl->data_to_match);
}

static bool isRealScheduleEvent(tSimStateHdl simHdl, const tEvent& ev)
{
  if (ev.fn == run_edge_schedule_event)
  {
    unsigned int n = ev.data.value;
    tClock         clk = get_clock_event_clk(n);
    tEdgeDirection dir = get_clock_event_dir(n);

    return (((dir == POSEDGE) && (simHdl->clocks[clk].on_posedge != NULL)) ||
            ((dir == NEGEDGE) && (simHdl->clocks[clk].on_negedge != NULL)));
  }
  else
    return (ev.fn == run_combo_schedule_event);
}

static bool isDummyScheduleEvent(tSimStateHdl simHdl, const tEvent& ev)
{
  if (ev.fn == run_edge_schedule_event)
  {
    unsigned int n = ev.data.value;
    tClock         clk = get_clock_event_clk(n);
    tEdgeDirection dir = get_clock_event_dir(n);

    return (((dir == POSEDGE) && (simHdl->clocks[clk].on_posedge == NULL)) ||
            ((dir == NEGEDGE) && (simHdl->clocks[clk].on_negedge == NULL)));
  }
  else
    return false;
}

static bool isStateDumpEvent(tSimStateHdl /* unused */, const tEvent& ev)
{
  return (ev.fn == dump_state_event);
}

static bool isCycleDumpEvent(tSimStateHdl /* unused */, const tEvent& ev)
{
  return (ev.fn == dump_cycle_event);
}

static bool isVCDEvent(tSimStateHdl /* unused */, const tEvent& ev)
{
  return (ev.fn == vcd_event);
}

static void add_dummy_schedule_events(tSimStateHdl simHdl)
{
  ++(simHdl->need_dummy_edges);
  if (simHdl->queue && (simHdl->need_dummy_edges == 1))
  {
    for (tClock clk = 0; clk < simHdl->clocks.size(); ++clk)
      setup_clock_edges(simHdl, clk);
  }
}

static void remove_dummy_schedule_events(tSimStateHdl simHdl)
{
  if (simHdl->need_dummy_edges == 0)
    return;

  --(simHdl->need_dummy_edges);

  if (simHdl->queue && (simHdl->need_dummy_edges == 0))
    simHdl->queue->remove(simHdl, isDummyScheduleEvent);
}

static void setup_reset_events(tSimStateHdl simHdl)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return;

  tEvent assert_event;
  assert_event.at = 0llu;
  assert_event.priority = make_priority(PG_INITIAL, PS_RESET);
  assert_event.fn = reset_model_event;
  assert_event.data.flag = true; // reset asserted

  tEvent deassert_event;
  deassert_event.at = 2llu;
  deassert_event.priority = make_priority(PG_AFTER_LOGIC, PS_RESET);
  deassert_event.fn = reset_model_event;
  deassert_event.data.flag = false; // reset deasserted

  simHdl->queue->schedule(assert_event);
  simHdl->queue->schedule(deassert_event);
}

static void setup_state_dump_events(tSimStateHdl simHdl, bool initial)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return;

  if (simHdl->last_state_dump_time == simHdl->sim_time)
    return;

  tEvent ev;

  ev.fn = dump_state_event;
  ev.at = simHdl->sim_time;
  ev.data.flag = initial;
  if (initial)
    ev.priority = make_priority(PG_INITIAL, PS_STATE_DUMP);
  else
    ev.priority = make_priority(PG_AFTER_LOGIC, PS_STATE_DUMP);

  if (!initial)
    simHdl->last_state_dump_time = simHdl->sim_time;

  simHdl->queue->schedule(ev);
}

static void setup_cycle_dump_events(tSimStateHdl simHdl)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return;

  // make an event for each real schedule event in the queue
  std::list<tEvent> new_events;
  for (const tEvent* pos = simHdl->queue->find(simHdl, isRealScheduleEvent);
       pos != NULL;
       pos = simHdl->queue->find(simHdl, NULL))
  {
    unsigned int n = pos->data.value;
    tClock clk = get_clock_event_clk(n);

    tEvent ev;
    ev.at         = pos->at;
    if (priority_group(pos->priority) == PG_INITIAL)
      ev.priority = make_priority(PG_INITIAL, PS_CYCLE_DUMP, clk);
    else
      ev.priority = make_priority(PG_BEFORE_LOGIC, PS_CYCLE_DUMP, clk);
    ev.fn         = dump_cycle_event;
    ev.data.value = n;

    new_events.push_front(ev);
  }

  // add new events to the queue
  for (std::list<tEvent>::const_iterator p = new_events.begin();
       p != new_events.end();
       ++p)
    simHdl->queue->schedule(*p);
  new_events.clear();
}

void setup_vcd_events(tSimStateHdl simHdl)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return;

  if (simHdl->queue->find(simHdl, isVCDEvent) == NULL)
  {
    // schedule the vcd event
    tEvent ev;
    ev.at        = simHdl->sim_time;
    ev.priority  = make_priority(PG_AFTER_LOGIC, PS_VCD);
    ev.fn        = vcd_event;
    ev.data.flag = false;

    simHdl->queue->schedule(ev);
  }
}

/*
 * Kernel API routines
 */

/* Get version information about the Bluesim model */
void bk_version(tSimStateHdl simHdl, tBluesimVersionInfo* version)
{
  if (version == NULL)
    return;
  (simHdl->model)->get_version(&(version->year),
			       &(version->month),
			       &(version->annotation),
			       &(version->build));
  version->creation_time = (simHdl->model)->get_creation_time();
}

/* helper routine for checking that model and kernel versions match */
bool check_version(tBluesimVersionInfo* version)
{
  return (year == version->year) &&
         (month == version->month) &&
         (((annotation == NULL) && (version->annotation == NULL)) ||
          ((annotation != NULL) && (version->annotation != NULL) &&
           !strcmp(annotation,version->annotation)));
}

/* Initialize the Bluesim kernel */
tSimStateHdl bk_init(tModel model, tBool master)
{
  tSimStateHdl simHdl = new tSimState;

  simHdl->model = (Model*)model;

  simHdl->sim_time = 0llu;
  simHdl->queue = NULL;

  simHdl->sim_running = false;
  simHdl->sim_shutting_down = false;
  simHdl->start_semaphore = NULL;
  simHdl->stop_semaphore = NULL;

  simHdl->in_combo_schedule = false;

  simHdl->stop_called = false;
  simHdl->finish_called = false;
  simHdl->abort_called = false;
  simHdl->exit_status = 0;
  simHdl->force_halt = false;

  simHdl->call_dump_state = false;
  simHdl->last_state_dump_time = 0llu;

  simHdl->call_dump_cycle_counts = false;

  simHdl->need_dummy_edges = 0;

  simHdl->rule_name_indent = 0;

  simHdl->reset_tick_requests = 0;

  (simHdl->vcd).state = VCD_OFF;
  (simHdl->vcd).vcd_filesize_limit = 0llu;
  (simHdl->vcd).go_xs = false;
  (simHdl->vcd).next_seq_num = 0;
  (simHdl->vcd).kept_seq_num = 0;
  (simHdl->vcd).is_backing_instance = false;

  (simHdl->vcd).min_pending = (simHdl->sim_time);
  (simHdl->vcd).last_time_written = (simHdl->sim_time);
  (simHdl->vcd).need_end_task = false;
  (simHdl->vcd).changes_now = false;

  (simHdl->vcd).vcd_file = NULL;
  (simHdl->vcd).vcd_enabled = false;
  (simHdl->vcd).vcd_checkpoint = false;
  (simHdl->vcd).vcd_depth = 0;

  // initialize directly so bk_set_timescale doesn't try to free garbage
  simHdl->sim_timescale = 1;
  (simHdl->vcd).vcd_timescale = strdup("1 us");

  tBluesimVersionInfo version;
  simHdl->model->get_version(&(version.year),
			     &(version.month),
			     &(version.annotation),
			     &(version.build));
  version.creation_time = simHdl->model->get_creation_time();
  if (! check_version(&version)) {
    fprintf(stderr,
	    "%s\n%s\n",
	    "Warning: the Bluesim kernel version does not match the BSC version used to",
	    "generate the Bluesim model");
  }
  init_mem_allocator();
  simHdl->sim_time = 0llu;
  simHdl->queue = new EventQueue();
  simHdl->need_dummy_edges = 0;
  simHdl->model->create_model(simHdl, master != 0);
  simHdl->top_symbol.key = "";
  simHdl->top_symbol.info = SYM_MODULE;
  simHdl->top_symbol.value = bk_get_model_instance(simHdl);
  simHdl->last_state_dump_time = ~(simHdl->sim_time);
  vcd_keep_ids(simHdl);

  /* setup simulation thread infrastructure */
  simHdl->force_halt = false;
  simHdl->sim_shutting_down = false;
  pthread_mutex_init(&(simHdl->sim_mutex), NULL);
  simHdl->start_semaphore = create_semaphore();
  simHdl->stop_semaphore = create_semaphore();
  if (simHdl->start_semaphore == NULL || simHdl->stop_semaphore == NULL)
  {
    release_semaphore(simHdl->start_semaphore);
    release_semaphore(simHdl->stop_semaphore);
    return NULL; // ERROR
  }

  /* start the simulation thread and wait for it to block in pause_sim */
  simHdl->sim_running = true;
  pthread_create(&(simHdl->sim_thread_id), NULL, sim_thread, (void*)simHdl);
  wait_for_sim_stop(simHdl);

  return simHdl;
}

/* Shutdown the Bluesim kernel */
void bk_shutdown(tSimStateHdl simHdl)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return;

  /* trigger the simulation queue thread to end */
  lock_sim_state(simHdl);
  simHdl->force_halt = true;
  simHdl->sim_shutting_down = true;
  unlock_sim_state(simHdl);
  post_semaphore(simHdl->start_semaphore);
  pthread_join(simHdl->sim_thread_id, NULL);
  simHdl->sim_running = false;

  /* clean up semaphores and mutexes */
  release_semaphore(simHdl->start_semaphore);
  simHdl->start_semaphore = NULL;
  release_semaphore(simHdl->stop_semaphore);
  simHdl->stop_semaphore = NULL;
  pthread_mutex_destroy(&(simHdl->sim_mutex));

  simHdl->model->destroy_model();
  shutdown_mem_allocator();
  for (unsigned int i = 0; i < simHdl->clocks.size(); ++i)
    free(simHdl->clocks[i].name);
  simHdl->clocks.clear();
  delete simHdl->queue;
  simHdl->queue = NULL;
  clear_plusargs(simHdl);
  vcd_reset(simHdl);
  delete simHdl;
}

/* Add edges into the event queue for a particular clock waveform.
 * The clock and direction are encoded in the event data.
 */
static void setup_clock_edges(tSimStateHdl simHdl, tClock clk)
{
  // if the clock has no predefined waveform, do not re-schedule events
  if ((simHdl->clocks[clk].low_phase_length == 0llu) &&
      (simHdl->clocks[clk].high_phase_length == 0llu))
    return;

  // otherwise, remove any existing schedule events for this clock

  simHdl->data_to_match = set_clock_event_data(clk, NEGEDGE);
  simHdl->queue->remove(simHdl, isMatchingScheduleEvent);
  simHdl->data_to_match = set_clock_event_data(clk, POSEDGE);
  simHdl->queue->remove(simHdl, isMatchingScheduleEvent);

  // and, add new schedule events for the altered clock

  // determine if the initial edge has already occurred
  bool initial_done = false;
  if (simHdl->sim_time > simHdl->clocks[clk].initial_delay)
    initial_done = true;
  else if ((simHdl->sim_time == simHdl->clocks[clk].initial_delay) &&
           (simHdl->clocks[clk].current_value != simHdl->clocks[clk].initial_value))
    initial_done = true;

  // setup the events correctly for the current time
  tEvent pos_ev, neg_ev, after_pos_ev, after_neg_ev;
  pos_ev.priority   = make_priority(PG_LOGIC, PS_EXECUTE, clk);
  pos_ev.fn         = run_edge_schedule_event;
  pos_ev.data.value = set_clock_event_data(clk, POSEDGE);

  after_pos_ev.priority   = make_priority(PG_FINAL, PS_COMBINATIONAL, clk);
  after_pos_ev.fn         = run_combo_schedule_event;
  after_pos_ev.data.value = set_clock_event_data(clk, POSEDGE);

  neg_ev.priority   = make_priority(PG_LOGIC, PS_EXECUTE, clk);
  neg_ev.fn         = run_edge_schedule_event;
  neg_ev.data.value = set_clock_event_data(clk, NEGEDGE);

  after_neg_ev.priority   = make_priority(PG_FINAL, PS_COMBINATIONAL, clk);
  after_neg_ev.fn         = run_combo_schedule_event;
  after_neg_ev.data.value = set_clock_event_data(clk, NEGEDGE);

  if (!initial_done)
  {
    // we need events for the initial edge and the following edge
    if (simHdl->clocks[clk].initial_value == CLK_LOW)
    {
      pos_ev.at = simHdl->clocks[clk].initial_delay;
      neg_ev.at = pos_ev.at + simHdl->clocks[clk].high_phase_length;
    }
    else
    {
      neg_ev.at = simHdl->clocks[clk].initial_delay;
      pos_ev.at = neg_ev.at + simHdl->clocks[clk].low_phase_length;
    }
  }
  else
  {
    // we need to determine the last true edge time and use it to
    // compute the next 2 edge times
    tTime pos = simHdl->clocks[clk].posedge_at;
    tTime neg = simHdl->clocks[clk].negedge_at;
    if (simHdl->clocks[clk].current_value == CLK_LOW)
    {
      // last edge was negative
      if (neg > pos)
        pos_ev.at = neg + simHdl->clocks[clk].low_phase_length;
      else
        pos_ev.at = pos + simHdl->clocks[clk].period;
      neg_ev.at = pos_ev.at + simHdl->clocks[clk].high_phase_length;
    }
    else
    {
      // last edge was positive
      if (pos > neg)
        neg_ev.at = pos + simHdl->clocks[clk].high_phase_length;
      else
        neg_ev.at = neg + simHdl->clocks[clk].period;
      pos_ev.at = neg_ev.at + simHdl->clocks[clk].low_phase_length;
    }
  }
  after_pos_ev.at = pos_ev.at;
  after_neg_ev.at = neg_ev.at;

  // if the initial waveform edge has not happened
  // and the simulation time is 0, then insert the time-0 edge
  // (the real "initial" edge -- if the clock has one)
  if ( (simHdl->clocks[clk].has_initial_value) &&
       (!initial_done) &&
       (simHdl->sim_time == 0) )
  {
    // XXX can this be reached when sim_time is 0 but the initial edge
    // XXX has already be executed -- in which case, we don't want to
    // XXX the initial execute it again?
    tEdgeDirection dir =
      ( simHdl->clocks[clk].initial_value == CLK_LOW ) ? NEGEDGE : POSEDGE ;
    tEvent init_ev;
    init_ev.at         = 0llu;
    init_ev.priority   = make_priority(PG_INITIAL, PS_EXECUTE, clk);
    init_ev.fn         = run_edge_schedule_event;
    init_ev.data.value = set_clock_event_data(clk, dir);
    simHdl->queue->schedule(init_ev);
  }

  // schedule the edge events we want in the queue
  if ((simHdl->need_dummy_edges > 0) || (simHdl->clocks[clk].on_posedge != NULL))
    simHdl->queue->schedule(pos_ev);
  if ((simHdl->need_dummy_edges > 0) || (simHdl->clocks[clk].on_negedge != NULL))
    simHdl->queue->schedule(neg_ev);
  if (simHdl->clocks[clk].after_posedge != NULL)
    simHdl->queue->schedule(after_pos_ev);
  if (simHdl->clocks[clk].after_negedge != NULL)
    simHdl->queue->schedule(after_neg_ev);
}

/* Define a clock waveform */
tClock bk_define_clock(tSimStateHdl simHdl,
		       const char* name,
                       tClockValue initial_value,
                       tBool       has_initial_value,
                       tTime       first_edge,
                       tTime       phase1_duration,
                       tTime       phase0_duration)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) || (name == NULL))
    return BAD_CLOCK_HANDLE;

  tClock clk = simHdl->clocks.size();

  tClockInfo ci;
  ci.name = strdup(name);
  ci.current_value = initial_value;
  ci.initial_value = initial_value;
  ci.has_initial_value = (has_initial_value != 0);
  ci.initial_delay = first_edge;
  ci.low_phase_length = phase0_duration;
  ci.high_phase_length = phase1_duration;
  ci.period = phase0_duration + phase1_duration;
  ci.negedge_at = 0llu;
  ci.posedge_at = 0llu;
  ci.combinational_at = 0llu;
  ci.on_posedge    = NULL;
  ci.after_posedge = NULL;
  ci.on_negedge    = NULL;
  ci.after_negedge = NULL;
  ci.posedge_count = 0llu;
  ci.negedge_count = 0llu;
  ci.posedge_limit = 0llu;
  ci.negedge_limit = 0llu;
  ci.vcd_num = vcd_reserve_ids(simHdl, 1);

  simHdl->clocks.push_back(ci);

  return clk;
}

/* Allow a clock definition to be altered (overridden from the UI, etc.) */
tStatus bk_alter_clock(tSimStateHdl simHdl,
		       tClock      clk,
                       tClockValue initial_value,
                       tBool       has_initial_value,
                       tTime       first_edge,
                       tTime       high_duration,
                       tTime       low_duration)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) ||
      (clk >= simHdl->clocks.size()))
    return BK_ERROR;

  simHdl->clocks[clk].current_value     = initial_value;
  simHdl->clocks[clk].initial_value     = initial_value;
  simHdl->clocks[clk].has_initial_value = (has_initial_value != 0);
  simHdl->clocks[clk].initial_delay     = first_edge;
  simHdl->clocks[clk].low_phase_length  = low_duration;
  simHdl->clocks[clk].high_phase_length = high_duration;
  simHdl->clocks[clk].period            = low_duration + high_duration;

  setup_clock_edges(simHdl, clk);

  return BK_SUCCESS;
}

/* Setup a callback for a clock event */
tStatus bk_set_clock_event_fn(tSimStateHdl simHdl,
			      tClock clk,
                              tScheduleFn on_edge_callback,
                              tScheduleFn after_edge_callback,
                              tEdgeDirection dir)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) ||
      (clk >= simHdl->clocks.size()))
    return BK_ERROR;

  if (dir == POSEDGE)
  {
    simHdl->clocks[clk].on_posedge    = on_edge_callback;
    simHdl->clocks[clk].after_posedge = after_edge_callback;
  }
  else
  {
    simHdl->clocks[clk].on_negedge    = on_edge_callback;
    simHdl->clocks[clk].after_negedge = after_edge_callback;
  }

  setup_clock_edges(simHdl, clk);

  return BK_SUCCESS;
}

/* Trigger a clock edge at a given time, for aperiodic clocks */
tStatus bk_trigger_clock_edge(tSimStateHdl simHdl,
			      tClock clk, tEdgeDirection dir, tTime at)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) ||
      (clk >= simHdl->clocks.size()) || (at < simHdl->sim_time))
    return BK_ERROR;

  if ( (simHdl->need_dummy_edges > 0) ||
       ((dir == POSEDGE) && (simHdl->clocks[clk].on_posedge != NULL)) ||
       ((dir == NEGEDGE) && (simHdl->clocks[clk].on_negedge != NULL)) )
  {
    tEvent ev, after_ev;
    ev.at         = at;
    ev.priority   = make_priority(PG_LOGIC, PS_EXECUTE, clk);
    ev.fn         = run_edge_schedule_event;
    ev.data.value = set_clock_event_data(clk, dir);
    after_ev.at         = at;
    after_ev.priority   = make_priority(PG_FINAL, PS_COMBINATIONAL, clk);
    after_ev.fn         = run_combo_schedule_event;
    after_ev.data.value = set_clock_event_data(clk, dir);
    simHdl->queue->schedule(ev);
    simHdl->queue->schedule(after_ev);
    return 1; /* events scheduled */
  }

  return 0; /* no events scheduled */
}

/* Enqueue an initial clock edge, for periodic and aperiodic clocks */
tStatus bk_enqueue_initial_clock_edge(tSimStateHdl simHdl,
				      tClock clk, tEdgeDirection dir)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) ||
      (clk >= simHdl->clocks.size()))
    return BK_ERROR;

  // XXX when a warning/error mechanism becomes available,
  // this would be a good place to warn
  if (simHdl->sim_time != 0llu)
    return BK_ERROR;

  if ( (simHdl->need_dummy_edges > 0) ||
       ((dir == POSEDGE) && (simHdl->clocks[clk].on_posedge != NULL)) ||
       ((dir == NEGEDGE) && (simHdl->clocks[clk].on_negedge != NULL)) )
  {
    tEvent ev;
    ev.at         = 0llu;
    ev.priority   = make_priority(PG_INITIAL, PS_EXECUTE, clk);
    ev.fn         = run_edge_schedule_event;
    ev.data.value = set_clock_event_data(clk, dir);
    simHdl->queue->schedule(ev);
    return 1; /* 1 event scheduled */
  }

  return 0; /* no events scheduled */
}

/* Lookup a clock handle by name */
tClock bk_get_clock_by_name(tSimStateHdl simHdl, const char* name)
{
  if (name)
  {
    tClock clk = simHdl->clocks.size();
    while (clk > 0)
    {
      if (!strcmp(name, simHdl->clocks[--clk].name))
        return clk;
    }
  }
  return BAD_CLOCK_HANDLE;
}

/* If there is already a clock domain with the given name,
 * return the handle for it.  If there is no clock domain with
 * this name yet, then create one and return the handle of the
 * new domain.  The domain characteristics can be set with
 * a subsequent call to bk_alter_clock().
 */
tClock bk_get_or_define_clock(tSimStateHdl simHdl, const char* name)
{
  // look for existing domain
  tClock clk = bk_get_clock_by_name(simHdl, name);
  if (clk != BAD_CLOCK_HANDLE)
    return clk;

  // no existing domain, so create one that must be toggled
  // using bk_trigger_clock_edge() or setup using bk_alter_clock().
  return (bk_define_clock(simHdl, name, CLK_LOW, 0, 0, 0, 0));
}

/* Get the number of clocks defined in the kernel */
tUInt32 bk_num_clocks(tSimStateHdl simHdl)
{
  return simHdl->clocks.size();
}

/* Get the clock handle for the nth clock.
 *
 * Returns the clock handle on success or BAD_CLOCK_HANDLE on error.
 */
tClock bk_get_nth_clock(tSimStateHdl simHdl, tUInt32 n)
{
  if (n >= simHdl->clocks.size())
    return BAD_CLOCK_HANDLE;
  else
    return ((tClock) n);
}

/* Get various information for a clock */

const char* bk_clock_name(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return NULL;
  return simHdl->clocks[clk].name;
}

tClockValue bk_clock_initial_value(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return CLK_LOW;
  return simHdl->clocks[clk].initial_value;
}

tTime bk_clock_first_edge(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return 0;
  return simHdl->clocks[clk].initial_delay;
}

tTime bk_clock_duration(tSimStateHdl simHdl, tClock clk, tClockValue value)
{
  if (clk >= simHdl->clocks.size())
    return 0;
  if (value == CLK_LOW)
    return simHdl->clocks[clk].low_phase_length;
  else
    return simHdl->clocks[clk].high_phase_length;
}

tClockValue bk_clock_val(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return CLK_LOW;

  return simHdl->clocks[clk].current_value;
}

tUInt64 bk_clock_cycle_count(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return 0llu;

  return std::max(simHdl->clocks[clk].posedge_count,
                  simHdl->clocks[clk].negedge_count);
}

tUInt64 bk_clock_edge_count(tSimStateHdl simHdl,
			    tClock clk, tEdgeDirection dir)
{
  if (clk >= simHdl->clocks.size())
    return 0llu;

  if (dir == POSEDGE)
    return simHdl->clocks[clk].posedge_count;
  else
    return simHdl->clocks[clk].negedge_count;
}

tUInt32 bk_clock_vcd_num(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return 0;
  return simHdl->clocks[clk].vcd_num;
}

/*
 * Setup a default reset waveform (asserted at time 0, deasserted at time 2).
 * This should be called before the first bk_advance() call.
 */
void bk_use_default_reset(tSimStateHdl simHdl)
{
  setup_reset_events(simHdl);
}

/*
 * Simulation control
 */

/* Get the current simulation time */
tTime bk_now(tSimStateHdl simHdl)
{
  return (simHdl->sim_timescale) * (simHdl->sim_time);
}

// A valid VCD unit is of the form: (1 | 10 | 100)<space>(s | ms | us | ns | ps | fs)
// The Verilog standard allows more whitespace, but that doesn't seem useful here.
// This test is ugly, but hopefully simple and correct.
bool valid_unit(const char* scale_unit) {
  std::string scale_unit_str(scale_unit);
  size_t unit_pos = 0;

  if(scale_unit_str.find("1 ") == 0) {
    unit_pos = 2;
  } else if(scale_unit_str.find("10 ") == 0) {
    unit_pos = 3;
  } else if(scale_unit_str.find("100 ") == 0) {
    unit_pos = 4;
  }

  // We didn't match a valid scale, so fail.
  if(unit_pos == 0)
    return false;

  std::string unit_str = scale_unit_str.substr(unit_pos);

  return (unit_str == "s"  || unit_str == "ms" || unit_str == "us" ||
          unit_str == "ns" || unit_str == "ps" || unit_str == "fs");
}

/* Set the simulation timescale */
tStatus bk_set_timescale(tSimStateHdl simHdl, const char* scale_unit, tTime scale_factor)
{
  if (simHdl->sim_time != 0)
    return BK_ERROR;

  if (!valid_unit(scale_unit))
    return BK_ERROR;

  simHdl->sim_timescale = scale_factor;
  char* current_timescale = simHdl->vcd.vcd_timescale;
  simHdl->vcd.vcd_timescale = strdup(scale_unit);
  if(current_timescale != NULL) {
    free(current_timescale);
  }

  return BK_SUCCESS;
}

/* Test if a given simulation time is still ongoing.
 * WARNING: This is a specialized function for use by
 * Bluesim primitives to facilitate connections to
 * event-driven simulation.  FOR EXPERT USE ONLY!
 *
 * Returns 1 (True) if the given simulation time is ongoing,
 * and 0 (False) otherwise.
 */
tBool bk_is_same_time(tSimStateHdl simHdl, tTime t)
{
  /* This access is not protected by a mutex, for performance reasons.
   * It should be safe to access, because this will only be called from
   * primitives during event execution, or from a SystemC wrapper after
   * bk_advance has returned.
   */
  if (simHdl->sim_running && (simHdl->sim_time == t))
    return 1;
  else
    return 0;
}

/* Test if we are currently executing within a combinational
 * schedule.
 * WARNING: This is a specialized function for use by Bluesim
 * primitives to facilitate clock-crossing implementations.
 * FOR EXPERT USE ONLY!
 *
 * Returns 1 (True) if currently executing a combinational schedule,
 * and 0 (False) otherwise.
 */
tBool bk_is_combo_sched(tSimStateHdl simHdl)
{
  /* This access is not protected by a mutex, for performance reasons.
   * It should be safe to access, because this will only be called from
   * primitives during event execution.
   */
  return simHdl->in_combo_schedule ? 1 : 0;
}

/* Get information on the clock event queue */

tTime bk_clock_last_edge(tSimStateHdl simHdl, tClock clk)
{
  if (clk >= simHdl->clocks.size())
    return ((tTime) 0llu);

  // Case 1: we are before the initial edge time
  if (simHdl->sim_time < simHdl->clocks[clk].initial_delay)
    return ((tTime) 0llu);

  // Case 2: we are at the time of the initial edge
  if (simHdl->sim_time == simHdl->clocks[clk].initial_delay)
  {
    if (simHdl->clocks[clk].current_value != simHdl->clocks[clk].initial_value)
      return (simHdl->sim_time);     // edge has already happened
    else
      return ((tTime) 0llu); // edge has not happened yet
  }

  // Case 3: we are beyond the first edge

  // Note: we are not guaranteed to have a schedule for both edges,
  // so we have to figure out which of the edge times is accurate.
  // We should trust the most recent edge time and reconstruct the
  // other one.  Also, for aperiodic clocks both edge times are
  // accurate.
  tTime pos = simHdl->clocks[clk].posedge_at;
  tTime neg = simHdl->clocks[clk].negedge_at;
  if (simHdl->clocks[clk].current_value == CLK_LOW)
  {
    // last edge was negedge, so determine the time
    if (neg > pos)
      return neg;
    else
      return (pos + simHdl->clocks[clk].high_phase_length);
  }
  else
  {
    // last edge was posedge, so determine the time
    if (pos > neg)
      return pos;
    else
      return (neg + simHdl->clocks[clk].low_phase_length);
  }
}

tTime bk_clock_combinational_time(tSimStateHdl simHdl, tClock clk)
{
  if (simHdl->queue && (clk < simHdl->clocks.size()))
    return simHdl->clocks[clk].combinational_at;

  return ((tTime) 0llu);
}

/* Simulation loop */

/* Quit simulation at the end of a given time slice */

void bk_quit_at(tSimStateHdl simHdl, tTime t)
{
  tEvent ev;
  ev.at       = t;
  ev.priority = make_priority(PG_FINAL, PS_UI);
  ev.fn       = quit_event;
  ev.data.ptr = NULL;
  simHdl->queue->schedule(ev);
}

tStatus bk_quit_after_edge(tSimStateHdl simHdl,
			   tClock clk, tEdgeDirection dir, tUInt64 cycle)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL) ||
      (clk >= simHdl->clocks.size()))
    return BK_ERROR;

  if (dir == POSEDGE)
    simHdl->clocks[clk].posedge_limit = cycle;
  else
    simHdl->clocks[clk].negedge_limit = cycle;

  return BK_SUCCESS;
}

/* Execute simulation events until none remain, simulation is
 * interrupted, or a stopping condition (time limit, etc.) is
 * encountered.
 */
tStatus bk_advance(tSimStateHdl simHdl, tBool async)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return BK_ERROR;

  /* check if the simulation is already running */
  if (bk_is_running(simHdl))
    return BK_ERROR;

  /* in case there was no bk_sync(), we want the stop semaphore to
   * return to 0.
   */
  trywait_on_semaphore(simHdl->stop_semaphore);

  /* kick off the simulation thread by posting to the start_semaphore */
  lock_sim_state(simHdl);
  simHdl->sim_running = true;
  unlock_sim_state(simHdl);
  post_semaphore(simHdl->start_semaphore);

  if (async)
    return BK_SUCCESS;  // don't wait for simulation to complete

  /* handle the synchronous case */
  wait_for_sim_stop(simHdl);

  return BK_SUCCESS;
}

/* Test if the simulation thread is still running.
 *
 * Returns 0 if the thread is not running and non-zero if
 * the thread is running.
 */
tBool bk_is_running(tSimStateHdl simHdl)
{
  tBool ret = 0;
  lock_sim_state(simHdl);
  if (simHdl->sim_running) ret = 1;
  unlock_sim_state(simHdl);
  return ret;
}

/* Wait for a simulation started using bk_advance in async mode
 * to complete.
 *
 * Returns the simulation time at which execution stopped.
 */
tTime bk_sync(tSimStateHdl simHdl)
{
  if (bk_is_running(simHdl))
    wait_for_sim_stop(simHdl);

  return simHdl->sim_time;
}

/* Schedule a UI callback for the end of a given timeslice,
 * if there is not already one scheduled at or before that time.
 *
 * Returns BK_ERROR on error or BK_SUCCESS on success.
 */
tStatus bk_schedule_ui_event(tSimStateHdl simHdl, tTime at)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return BK_ERROR;

  simHdl->target_yield_time = at;
  if (simHdl->queue->find(simHdl, isMatchingYieldEvent) == NULL)
  {
    tEvent event;
    event.at       = at;
    event.priority = make_priority(PG_FINAL, PS_UI);
    event.data.ptr = NULL;
    event.fn       = yield_event;

    simHdl->queue->schedule(event);
  }

  return BK_SUCCESS;
}

/* Remove a UI callback previously scheduled at the end of a given timeslice.
 *
 * Returns BK_ERROR on error or BK_SUCCESS on success.
 */
tStatus bk_remove_ui_event(tSimStateHdl simHdl, tTime at)
{
  if ((simHdl == NULL) || (simHdl->queue == NULL))
    return BK_ERROR;

  simHdl->target_yield_time = at;
  simHdl->queue->remove(simHdl, isMatchingYieldEvent);

  return BK_SUCCESS;
}

/* Control dumping of state */

void bk_enable_state_dumping(tSimStateHdl simHdl)
{
  simHdl->call_dump_state = true;
  setup_state_dump_events(simHdl, true);
}

void bk_disable_state_dumping(tSimStateHdl simHdl)
{
  simHdl->call_dump_state = false;
  if (simHdl->queue)
    simHdl->queue->remove(simHdl, isStateDumpEvent);
}

tBool bk_is_state_dumping_enabled(tSimStateHdl simHdl)
{
  return simHdl->call_dump_state ? 1 : 0;
}

void bk_dump_state(tSimStateHdl simHdl, const char* label)
{
  printf("%s:\n", label);
  simHdl->model->dump_state();
}

/* Control dumping of cycle counts */

void bk_enable_cycle_dumping(tSimStateHdl simHdl)
{
  if (!simHdl->call_dump_cycle_counts)
  {
    simHdl->call_dump_cycle_counts = true;
    setup_cycle_dump_events(simHdl);
  }
}

void bk_disable_cycle_dumping(tSimStateHdl simHdl)
{
  simHdl->call_dump_cycle_counts = false;
  if (simHdl->queue)
    simHdl->queue->remove(simHdl, isCycleDumpEvent);
}

tBool bk_is_cycle_dumping_enabled(tSimStateHdl simHdl)
{
  return simHdl->call_dump_cycle_counts ? 1 : 0;
}

void bk_dump_cycle_counts(tSimStateHdl simHdl, const char* label, tClock clk)
{
  unsigned int indent = 0;
  if (label)
  {
    printf("%s: ", label);
    indent = strlen(label) + 2;
  }
  if (clk >= simHdl->clocks.size())
  {
    for (tClock n = 0; n < simHdl->clocks.size(); ++n)
    {
      if (n > 0 && indent != 0)
        printf("%*s", indent, "");
      printf("%llu %s cycles\n",
             bk_clock_cycle_count(simHdl, n), simHdl->clocks[n].name);
    }
  }
  else
    printf("%llu %s cycles\n",
           bk_clock_cycle_count(simHdl, clk), simHdl->clocks[clk].name);
}

/* Control dumping of VCD */

tBool bk_enable_VCD_dumping(tSimStateHdl simHdl)
{
  if ((simHdl->vcd).vcd_enabled)
    return 1;
  else if (vcd_set_state(simHdl, true))
  {
    add_dummy_schedule_events(simHdl);
    return 1;
  }
  else
    return 0;
}

void bk_disable_VCD_dumping(tSimStateHdl simHdl)
{
  if (!(simHdl->vcd).vcd_enabled)
    return;

  if (simHdl->queue)
    simHdl->queue->remove(simHdl, isVCDEvent);

  remove_dummy_schedule_events(simHdl);
  vcd_set_state(simHdl, false);
  vcd_dump_xs(simHdl);
}

tBool bk_is_VCD_dumping_enabled(tSimStateHdl simHdl)
{
  return (simHdl->vcd).vcd_enabled ? 1 : 0;
}

/* Used by SystemC wrappers to update VCD values at non-standard times.
 * Look no further for evidence that Bluesim's VCD handling is a mess.
 */
void bk_VCD_combo_update(tSimStateHdl simHdl, tTime t)
{
  if (!(simHdl->vcd).vcd_enabled)
    return;

  // schedule a special "immediate" vcd event
  tEvent ev;
  ev.at        = t;
  ev.priority  = make_priority(PG_BEFORE_LOGIC, PS_VCD);
  ev.fn        = vcd_event;
  ev.data.flag = true;

  simHdl->queue->schedule(ev);
}

/* Call to enable clock edges without logic (for interactive stepping) */
void bk_set_interactive(tSimStateHdl simHdl)
{
  add_dummy_schedule_events(simHdl);
}

/* Stop simulation now */
void bk_stop_now(tSimStateHdl simHdl, tSInt32 status)
{
  simHdl->stop_called = true;
  simHdl->exit_status = status;
  bk_schedule_ui_event(simHdl, simHdl->sim_time);
}

/* End simulation */
void bk_finish_now(tSimStateHdl simHdl, tSInt32 status)
{
  simHdl->finish_called = true;
  simHdl->exit_status = status;
  bk_schedule_ui_event(simHdl, simHdl->sim_time);
}

tBool bk_stopped(tSimStateHdl simHdl)
{
  return simHdl->stop_called ? 1 : 0;
}

tBool bk_finished(tSimStateHdl simHdl)
{
  return simHdl->finish_called ? 1 : 0;
}

tSInt32 bk_exit_status(tSimStateHdl simHdl)
{
  return simHdl->exit_status;
}

/* Abort simulation (from outside, Ctrl-C, SIGPIPE, etc.) */
void bk_abort_now(tSimStateHdl simHdl)
{
  if (bk_is_running(simHdl))
  {
    simHdl->abort_called = true;
    simHdl->force_halt = true;
  }
}

tBool bk_aborted(tSimStateHdl simHdl)
{
  return simHdl->abort_called ? 1 : 0;
}

/* Routine which provides direct access to the top-level model.  This
 * should only be used by callers that know exactly what they are doing.
 */
void* bk_get_model_instance(tSimStateHdl simHdl)
{
  return simHdl->model->get_instance();
}

/* Get the symbol for the top module. */
tSymbol bk_top_symbol(tSimStateHdl simHdl)
{
  return &(simHdl->top_symbol);
}

/* Lookup a symbol by name.  Returns BAD_SYMBOL if the named
 * symbol is not found.
 */
tSymbol bk_lookup_symbol(tSymbol root, const char* name)
{
  tSymbol sym = root;

  if (name == NULL) return BAD_SYMBOL;

  while ((sym != BAD_SYMBOL) && bk_is_module(sym))
  {
    Module* mod = (Module*) bk_get_ptr(sym);
    const char* cptr = strchr(name,'.');
    unsigned int len = (cptr == NULL) ? strlen(name) : (cptr - name);
    sym = mod->lookup(name,len);
    name += len;
    if (*name == '\0') break;
    ++name;  // skip "."
  };

  return sym;
}

/* Test if a symbol represents a module */
tBool bk_is_module(tSymbol sym)
{
  return (get_symtag(sym) == SYM_MODULE) ? 1 : 0;
}

/* Test if a symbol represents a rule */
tBool bk_is_rule(tSymbol sym)
{
  return (get_symtag(sym) == SYM_RULE) ? 1 : 0;
}

/* Test if a symbol represents a value */
tBool bk_is_single_value(tSymbol sym)
{
  switch (get_symtag(sym))
  {
   case SYM_DEF:
   case SYM_PARAM:
   case SYM_PORT:
   case SYM_COMPUTED:
     return 1;
   default:
     return 0;
  }
}

/* Test if a symbol represents a range of values */
tBool bk_is_value_range(tSymbol sym)
{
  return (get_symtag(sym) == SYM_RANGE) ? 1 : 0;
}

/* Get a pointer to the value for a value symbol.
 * Returns NULL for other symbol types.
 */
const unsigned int* bk_peek_symbol_value(tSymbol sym)
{
  if (sym == BAD_SYMBOL) return NULL;

  switch (get_symtag(sym))
  {
    case SYM_DEF:
    case SYM_PARAM:
    case SYM_PORT:
    {
      unsigned int sz = bk_get_size(sym);
      void* ptr = bk_get_ptr(sym);
      return (symbol_value(ptr,sz));
    }
    default:
      return NULL;
  }
}

/* Get the minimum address for value range.
 * Returns NULL for other symbol types.
 */
tUInt64 bk_get_range_min_addr(tSymbol sym)
{
  if (bk_is_value_range(sym))
  {
    Range* range = (Range*) bk_get_ptr(sym);
    return range->lo;
  }

  return (tUInt64) 0;
}

/* Get the maximum address for a value range.
 * Returns NULL for other symbol types.
 */
tUInt64 bk_get_range_max_addr(tSymbol sym)
{
  if (bk_is_value_range(sym))
  {
    Range* range = (Range*) bk_get_ptr(sym);
    return range->hi;
  }

  return (tUInt64) 0;
}

/* Get a pointer to a value selected from a range.
 * Returns NULL for other symbol types, or if the address is out of bounds.
 */
const unsigned int* bk_peek_range_value(tSymbol sym, tUInt64 addr)
{
  if (bk_is_value_range(sym))
  {
    Range* range = (Range*) bk_get_ptr(sym);
    return range->fetch(range->base,addr);
  }

  return NULL;
}

/* Get the number of sub-symbols of a module.
 * Returns 0 for other symbol types.
 */
tUInt32 bk_num_symbols(tSymbol sym)
{
  if (sym == BAD_SYMBOL) return 0;

  if (bk_is_module(sym))
  {
    Module* mod = (Module*) bk_get_ptr(sym);
    return mod->num_symbols();
  }
  else
    return 0;
}

/* Get the Nth sub-symbol of a module (starting at 0).
 * Returns BAD_SYMBOL for other symbol types.
 */
tSymbol bk_get_nth_symbol(tSymbol sym, tUInt32 n)
{
  if (sym == BAD_SYMBOL) return BAD_SYMBOL;

  if (bk_is_module(sym))
  {
    Module* mod = (Module*) bk_get_ptr(sym);
    return mod->nth_symbol(n);
  }
  else
    return BAD_SYMBOL;
}
