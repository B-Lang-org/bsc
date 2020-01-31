#ifndef __PRIORITY_H__
#define __PRIORITY_H__

#include "bluesim_types.h"

// Priority within a time slice for ordering events
typedef unsigned int tPriority;

/* The priority value is broken down into fields:
 *   Bits 31-28: groups which divide a time slice into
 *               initialization, before logic, logic, etc.
 *   Bits 27-24: slots which further subdivide groups into
 *               reset events, UI events, etc.
 *   Bits 23-0:  24 bits of clock number, for ordering simultaneous
 *               events consistently based on their associated clock.
 */

typedef enum {
  PG_INITIAL,
  PG_BEFORE_LOGIC,
  PG_LOGIC,
  PG_AFTER_LOGIC,
  PG_FINAL
} tPriorityGroup;

typedef enum {
  PS_RESET,
  PS_UI,
  PS_CYCLE_DUMP,
  PS_VCD,
  PS_EXECUTE,
  PS_RULE_DUMP,
  PS_STATE_DUMP,
  PS_COMBINATIONAL
} tPrioritySlot;

// These functions are used to construct and access a priority
tPriority make_priority(tPriorityGroup g, tPrioritySlot s, tClock clk = 0);
tPriorityGroup priority_group(tPriority p);
tPrioritySlot  priority_slot(tPriority p);
tClock         priority_clock(tPriority p);

// debug functions for displaying priority info
const char* priority_group_name(tPriorityGroup g);
const char* priority_slot_name(tPrioritySlot s);

#endif /* __PRIORITY_H__ */
