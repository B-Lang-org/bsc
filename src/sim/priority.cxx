#include "priority.h"

tPriority make_priority(tPriorityGroup g, tPrioritySlot s, tClock clk)
{
  return ((g << 28)          |
	  ((s & 0xF) << 24)  |
          (clk & 0x00FFFFFF));
}

tPriorityGroup priority_group(tPriority p)
{
  return (tPriorityGroup) (p >> 28);
}

tPrioritySlot priority_slot(tPriority p)
{
  return (tPrioritySlot) ((p >> 24) & 0xF);
}

tClock priority_clock(tPriority p)
{
  return (tClock) (p & 0x00FFFFFF);
}

// debug functions for displaying priority info
const char* priority_group_name(tPriorityGroup g)
{
  switch (g)
  {
    case PG_INITIAL:      return "INITIAL";
    case PG_BEFORE_LOGIC: return "BEFORE LOGIC";
    case PG_LOGIC:        return "LOGIC";
    case PG_AFTER_LOGIC:  return "AFTER LOGIC";
    case PG_FINAL:        return "FINAL";
  }

  return "?";
}

const char* priority_slot_name(tPrioritySlot s)
{
  switch (s)
  {
    case PS_RESET:         return "RESET";
    case PS_UI:            return "UI";
    case PS_CYCLE_DUMP:    return "CYCLE DUMP";
    case PS_VCD:           return "VCD";
    case PS_EXECUTE:       return "EXECUTE";
    case PS_RULE_DUMP:     return "RULE DUMP";
    case PS_STATE_DUMP:    return "STATE DUMP";
    case PS_COMBINATIONAL: return "COMBINATIONAL";
  }

  return "?";
}
