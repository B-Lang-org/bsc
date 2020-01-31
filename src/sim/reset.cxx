/* These routines are used to allow the schedule code to
 * handle resets.  Since reset should be a very small percentage
 * of the simulation, we want to minimize the cost of testing
 * for reset and we are less concerned with the actual cost of
 * processing when reset is active.
 *
 * Primitives that are reset synchronously but have asynchronous
 * input resets need to delay entry into reset until the next clock
 * edge for the primitive.  During normal operation, they may not
 * need to do anything on each clock edge, and we want to avoid them
 * having a permanent tick() method that slows down non-reset cycles.
 * So we partition the tick methods into the permanent ones and the
 * reset ones and only execute the reset ones (all of them) when
 * some primitive (even if it is only one) requires it.
 */

#include "bs_reset.h"
#include "kernel.h"
#include "event_queue.h"
#include "bs_vcd.h"

/* Keep a list of pending reset calls */
typedef struct
{
  tResetFn fn;
  tUInt8   rst;
  void*    parent;
} tResetRequest;

/* Initialize the reset request counting system */
void init_reset_request_counters(tSimStateHdl simHdl)
{
  simHdl->reset_tick_requests = 0;
}

/* Test if a any primitive still needs reset ticks */
bool do_reset_ticks(tSimStateHdl simHdl)
{
  return (simHdl->reset_tick_requests > 0);
}

/* Record a request for reset ticks from a primitive */
void start_reset_ticks(tSimStateHdl simHdl)
{
  ++(simHdl->reset_tick_requests);
}

/* Withdraw a request for reset ticks from a primitive */
void stop_reset_ticks(tSimStateHdl simHdl)
{
  if (simHdl->reset_tick_requests > 0)
    --(simHdl->reset_tick_requests);
}


/* Routine called from kernel to execute delayed reset functions */
static tTime reset_event(tSimStateHdl simHdl, tEvent& ev)
{
  if (ev.data.ptr == NULL)
    return 0llu;

  tResetRequest* req = (tResetRequest*) ev.data.ptr;

  if (req->fn == NULL)
    return 0llu;
  
  req->fn(req->parent, req->rst);
  if (req->rst == 0)
    start_reset_ticks(simHdl);
  else
    stop_reset_ticks(simHdl);

  delete req;

  return 0llu;
}

/* Queue a reset function to be called at the beginning of the time-slice */
void reset_init(tSimStateHdl simHdl, tResetFn fn, void* parent, tUInt8 rst)
{
  if (vcd_is_backing_instance(simHdl))
    return;

  tResetRequest* req = new tResetRequest;

  req->fn     = fn;
  req->parent = parent;
  req->rst    = rst;

  tEvent ev;

  ev.at       = simHdl->sim_time;
  ev.priority = make_priority(PG_INITIAL, PS_RESET);
  ev.fn       = reset_event;
  ev.data.ptr = req;

  simHdl->queue->schedule(ev);
}

/* Queue a reset function to be called at the end of the time-slice */
void reset_at_end_of_timeslice(tSimStateHdl simHdl,
			       tResetFn fn, void* parent, tUInt8 rst)
{
  if (vcd_is_backing_instance(simHdl))
    return;

  tResetRequest* req = new tResetRequest;

  req->fn     = fn;
  req->parent = parent;
  req->rst    = rst;

  tEvent ev;

  ev.at       = simHdl->sim_time;
  ev.priority = make_priority(PG_AFTER_LOGIC, PS_RESET);
  ev.fn       = reset_event;
  ev.data.ptr = req;

  simHdl->queue->schedule(ev);
}
