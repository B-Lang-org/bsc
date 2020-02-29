#ifndef __BS_RESET_H__
#define __BS_RESET_H__

#include "bluesim_types.h"

/* Routines called from the schedule to determine if reset
 * tick calls are required.
 */
void init_reset_request_counters(tSimStateHdl simHdl);
bool do_reset_ticks(tSimStateHdl simHdl);

/* Routines called from primitives to control reset period */
void start_reset_ticks(tSimStateHdl simHdl);
void stop_reset_ticks(tSimStateHdl simHdl);

/* Routine called from primitives to trigger delayed reset function */
void reset_init(tSimStateHdl simHdl, tResetFn fn, void* parent, tUInt8 rst);
void reset_at_end_of_timeslice(tSimStateHdl simHdl,
			       tResetFn fn, void* parent, tUInt8 rst);

#endif /* __BS_RESET_H__ */

