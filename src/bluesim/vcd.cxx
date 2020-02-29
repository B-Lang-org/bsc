#include <time.h>
#include <cstdio>
#include <cstring>
#include <string>

#include "bluesim_kernel_api.h"
#include "kernel.h"
#include "bs_vcd.h"
#include "bs_target.h"
#include "portability.h"  // need port_ftello

// VCD generator version
static const unsigned int major_rev = 2;
static const unsigned int minor_rev = 1;

/* VCD change buffer mechanism
 *
 * Bluesim computes all changes at the posedge, according to TRS
 * semantics, but the expected output of VCD (to match Verilog)
 * requires that the combinational logic values take on their new
 * values after the previous posedge.
 *
 * This means that on the posedge, we need to be able to assign
 * changes of combinational logic to a previous time and assign
 * changes of state values to the current time.
 * 
 * So we keep track of the clocks for each signal and use that
 * information to determine the delay between an eager evaluation
 * (Verilog-style) and a lazy evaluation (Bluesim-style).  The
 * calculated delay for each signal is used to correct the VCD times.
 *
 * VCD changes are buffered and accumulated until all clocks which
 * can assign a change to that time have occured, at which point
 * changes for that time are written to the VCD file.
 */ 

tStatus bk_set_VCD_file(tSimStateHdl simHdl, const char* name)
{
  tVCDState* s = &(simHdl->vcd);

  if (s->vcd_file != NULL)
    fclose(s->vcd_file);
  s->vcd_file_name.resize(0);

  s->state = VCD_OFF;
  if (name == NULL)
  {
    s->vcd_file = NULL;
    return BK_SUCCESS;
  }

  s->vcd_file_name = name;
  if (s->previous_files.find(s->vcd_file_name) != s->previous_files.end())
  {
    // if we are returning to a previous file, do not write the header again
    s->vcd_file = fopen(name, "a");
    s->state = VCD_DISABLED;
  }
  else
    s->vcd_file = fopen(name, "w");

  if (s->vcd_file == NULL)
  {
    s->vcd_file_name.resize(0);
    perror(name);
    return BK_ERROR;
  }

  return BK_SUCCESS;
}

const char* bk_get_VCD_file_name(tSimStateHdl simHdl)
{
  return (simHdl->vcd).vcd_file_name.c_str();
}

void bk_set_VCD_depth(tSimStateHdl simHdl, tUInt32 depth)
{
  if ((simHdl->vcd).state == VCD_OFF)
    (simHdl->vcd).vcd_depth = depth;
}

tStatus bk_VCD_checkpoint(tSimStateHdl simHdl)
{
  if ((simHdl->vcd).vcd_file == NULL)
  {
    if (bk_set_VCD_file(simHdl, "dump.vcd") != BK_SUCCESS)
      return BK_ERROR;
  }

  (simHdl->vcd).vcd_checkpoint = true;

  return BK_SUCCESS;
}

void bk_set_VCD_filesize_limit(tSimStateHdl simHdl, tUInt64 bytes)
{
  (simHdl->vcd).vcd_filesize_limit = bytes;
}

void bk_flush_VCD_output(tSimStateHdl simHdl)
{
  if ((simHdl->vcd).vcd_file != NULL)
    fflush((simHdl->vcd).vcd_file);
}

/* VCD routines used by the simulation kernel */

// forward declarations
static void flush_changes(tSimStateHdl simHdl);
static void print_X(tSimStateHdl simHdl, unsigned int bits, unsigned int num);
static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, tUInt64 val);
static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, const tUWide& val);

void vcd_reset(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);

  s->changes_now = false;
  s->min_pending = bk_now(simHdl);
  flush_changes(simHdl);
  if (s->vcd_file != NULL)
    fclose(s->vcd_file);
  s->vcd_file = NULL;
  if (! s->vcd_file_name.empty())
    s->vcd_file_name.resize(0);
  s->previous_files.clear();
  s->state = VCD_OFF;
  s->vcd_enabled = false;
  s->vcd_depth = 0;
  s->vcd_filesize_limit = 0llu;
  s->vcd_checkpoint = false;
  s->go_xs = false;
  s->next_seq_num = 0;
  s->kept_seq_num = 0;
  s->is_backing_instance = false;
  s->clk_map.clear();
  s->changes.clear();
  s->tasks.clear();
  s->last_time_written = ~bk_now(simHdl);
  s->need_end_task = false;
}

void vcd_task(tSimStateHdl simHdl, const char* task)
{
  (simHdl->vcd).tasks[bk_now(simHdl)] = task;
}

void vcd_dump_xs(tSimStateHdl simHdl)
{
  (simHdl->vcd).go_xs = true;
}

bool vcd_set_state(tSimStateHdl simHdl, bool enabled)
{
  if (enabled && ((simHdl->vcd).vcd_file == NULL))
  {
    if (bk_set_VCD_file(simHdl, "dump.vcd") != BK_SUCCESS)
      return false;
  }

  (simHdl->vcd).vcd_enabled = enabled;

  return true;
}

bool vcd_is_active(tSimStateHdl simHdl)
{
  return ((simHdl->vcd).vcd_enabled ||
	  (simHdl->vcd).vcd_checkpoint ||
	  (simHdl->vcd).go_xs);
}

tVCDDumpType get_VCD_dump_type(tSimStateHdl simHdl)
{
  tVCDDumpType ret;
  tVCDState* s = &(simHdl->vcd);

  if (s->vcd_checkpoint)
  {
    ret = VCD_DUMP_CHECKPOINT;
    s->vcd_checkpoint = false;
    s->go_xs = ! s->vcd_enabled;
  }
  else if (s->go_xs)
  {
    ret = VCD_DUMP_XS;
    s->go_xs = false;
    s->state = VCD_DISABLED;
  }
  else
  {
    switch (s->state)
    {
      case VCD_HEADER:   { ret = VCD_DUMP_INITIAL; break; }
      case VCD_ENABLED:  { ret = VCD_DUMP_CHANGES; break; }
      case VCD_DISABLED: { ret = VCD_DUMP_RESTART; break; }
      default:           { ret = VCD_DUMP_NONE; break; }
    }
    s->state = VCD_ENABLED;
  }

  return ret;
}

bool vcd_write_header(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);

  if (s->vcd_file == NULL)
    return false;

  if (s->state != VCD_OFF)
    return false;

  s->state = VCD_HEADER;

  FileTarget dest(s->vcd_file);

  time_t t = time(NULL);
  dest.write_string("$date\n\t%s$end\n", ctime(&t));
  dest.write_string("$version\n");
  dest.write_string("\tBluespec VCD dumper %d.%d\n", major_rev, minor_rev);
  dest.write_string("$end\n");
  dest.write_string("$timescale\n\t%s\n$end\n", s->vcd_timescale);

  s->next_seq_num = s->kept_seq_num;

  return true;
}

bool vcd_check_file_size(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);
  if ((s->vcd_file != NULL) && (s->vcd_filesize_limit != 0llu))
  {
    unsigned long long sz = (unsigned long long) port_ftello(s->vcd_file);
    if (sz > s->vcd_filesize_limit)
    {
      vcd_write_comment(simHdl, "VCD file size limit exceeded\n");
      vcd_reset(simHdl);
      return false;
    }
  }
  return true;
}

void vcd_write_comment(tSimStateHdl simHdl, const char* comment)
{
  FileTarget dest((simHdl->vcd).vcd_file);
  dest.write_string("$comment\n%s$end\n", comment);
}

void vcd_set_backing_instance(tSimStateHdl simHdl, bool b)
{
  (simHdl->vcd).is_backing_instance = b;
}


/* VCD routines called from modules */

tUInt32 vcd_depth(tSimStateHdl simHdl)
{
  return (simHdl->vcd).vcd_depth;
}

bool vcd_is_backing_instance(tSimStateHdl simHdl)
{
  return (simHdl->vcd).is_backing_instance;
}

unsigned int vcd_reserve_ids(tSimStateHdl simHdl, unsigned int num)
{
  unsigned int n = (simHdl->vcd).next_seq_num;
  (simHdl->vcd).next_seq_num += num;
  return n;
}

void vcd_keep_ids(tSimStateHdl simHdl)
{
  (simHdl->vcd).kept_seq_num = (simHdl->vcd).next_seq_num;
}

void vcd_write_id(tSimStateHdl simHdl, unsigned int num)
{
  char buf[6];
  char* cptr = buf + 6;
  unsigned int len = 0;
  *(--cptr) = '\0';
  do {
    *(--cptr) = '!' + (num % 94);
    num = num / 94;
    ++len;
  } while (num > 0);
  FileTarget dest((simHdl->vcd).vcd_file);
  dest.write_data(cptr,sizeof(char),len);
}

static bool match_hierarchy(Module* module,
			    const char* s, int depth = -1)
{
  if (s == NULL) return false;
  if (module == NULL) return (depth == 0);

  // if depth < 0, then determine the starting depth
  if (depth < 0)
  {
    const char* ptr = s;
    depth = 0;
    while (*ptr)
    {
      if (*ptr++ == '.') ++depth;
    }
  }

  if (depth == 0) return (module->parent == NULL);

  // locate the hierarchy segment at this depth
  int level = 1;
  const char* start = (depth == 1) ? s : NULL;
  unsigned int len = 0;
  const char* ptr = s;
  while (*ptr)
  {
    if (*ptr == '.')
    {
      if (depth == level) break;
      ++depth;
      if (depth == level)
      {
	start = ptr;
	len = 1;
      }
    }
    ++ptr;
  }

  // test if this hierarchy segment matches the module
  if (!strncmp(module->inst_name, start, len))
    return false;

  // we matched, so check the next level up
  return match_hierarchy(module->parent, s, depth-1);
}

void vcd_add_clock_def(tSimStateHdl simHdl,
		       Module* module, const char* s, unsigned int num)
{
  if (match_hierarchy(module,s))
  {
    fputs("$var reg 1 ", (simHdl->vcd).vcd_file);
    vcd_write_id(simHdl, num);
    fprintf((simHdl->vcd).vcd_file, " %s $end\n", s);
  }
}

void vcd_set_clock(tSimStateHdl simHdl, unsigned int num, tClock handle)
{
  if (handle == BAD_CLOCK_HANDLE)
    return;
  
  (simHdl->vcd).clk_map.insert(std::make_pair(num,handle));
}

void vcd_write_scope_start(tSimStateHdl simHdl, const char* name)
{
  fprintf((simHdl->vcd).vcd_file, "$scope module %s $end\n", name);
}

void vcd_write_scope_end(tSimStateHdl simHdl)
{
  fprintf((simHdl->vcd).vcd_file, "$upscope $end\n");
}

void vcd_write_def(tSimStateHdl simHdl,
		   unsigned int num,
		   const char* name,
		   unsigned int width)
{
  FileTarget dest((simHdl->vcd).vcd_file);
  dest.write_string("$var reg %d ", width);
  vcd_write_id(simHdl, num);
  dest.write_string(" %s $end\n", name);  
}

void vcd_advance(tSimStateHdl simHdl, bool immediate)
{
  /* update the min_pending value */
  (simHdl->vcd).min_pending = bk_now(simHdl);
  for (tClock clk = 0; clk < bk_num_clocks(simHdl); ++clk)
  {
    tTime le = bk_clock_combinational_time(simHdl, clk);
    if (le < (simHdl->vcd).min_pending)
      (simHdl->vcd).min_pending = le;
  }

  /* write all changes prior to min_pending */
  flush_changes(simHdl);

  /* update changes_now setting */
  (simHdl->vcd).changes_now = immediate;
}

static void flush_changes(tSimStateHdl simHdl)
{
  for (std::map<tTime,tChangeList>::iterator cl = (simHdl->vcd).changes.begin();
       cl != (simHdl->vcd).changes.end();
       )
  {
    tTime t = cl->first;
    if (t >= (simHdl->vcd).min_pending)
      return;

    vcd_output_at_time(simHdl, t);

    /* Print all VCD entries for this time */
    tChangeList& ch_list = cl->second;
    for (tChangeList::iterator p = ch_list.begin();
         p != ch_list.end();
         ++p)
    {
      Change& ch = *p;
      if (ch.isX)
        print_X(simHdl, ch.bits, ch.num);
      else if (ch.bits <= 64)
        print_change(simHdl, ch.bits, ch.num, ch.narrow);
      else
        print_change(simHdl, ch.bits, ch.num, ch.wide);
    }

    (simHdl->vcd).changes.erase(cl++);
  }
}

void vcd_output_at_time(tSimStateHdl simHdl, tTime time)
{
  if ((simHdl->vcd).last_time_written == time)
    return;

  (simHdl->vcd).last_time_written = time;

  FileTarget dest((simHdl->vcd).vcd_file);

  if ((simHdl->vcd).need_end_task)
    dest.write_string("$end\n");

  dest.write_string("#%llu\n", time);

  /* If there is a task name associated with this time, print it */
  std::map<tTime, const char*>::iterator p = (simHdl->vcd).tasks.find(time);
  if (p != (simHdl->vcd).tasks.end())
  {
    (simHdl->vcd).need_end_task = true;
    dest.write_string("%s\n", p->second);
    (simHdl->vcd).tasks.erase(p);
  }
  else
    (simHdl->vcd).need_end_task = false;
}

static tTime time_of_change(tSimStateHdl simHdl, unsigned int num)
{
  std::pair<tClockMap::iterator,tClockMap::iterator> p
    = (simHdl->vcd).clk_map.equal_range(num);

  // if we are in an immediate update situation, use the current time
  if ((simHdl->vcd).changes_now)
    return bk_now(simHdl);
  
  // if there is no associated clock, use the current time
  if (p.first == p.second)
    return bk_now(simHdl);

  // otherwise, find the most recent combinational time of
  // any associated clock
  tTime recent = 0llu;
  tClockMap::iterator iter = p.first;
  while (iter != p.second)
  {
    tClock handle = iter->second;
    tTime le = bk_clock_combinational_time(simHdl, handle);
    if (le > recent)
      recent = le;
    ++iter;
  }

  return recent;
}

void vcd_write_x(tSimStateHdl simHdl,
		 unsigned int num,
                 unsigned int width)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num,width));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_X(simHdl, width, num);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   tClockValue value,
		   unsigned int /* unused */)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, 1, (value == CLK_HIGH) ? 1 : 0));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, 1, num, (value == CLK_HIGH) ? 1 : 0);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   bool value,
		   unsigned int /* unused */)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, 1, value ? 1 : 0));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, 1, num, value ? 1 : 0);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   tUInt8 value,
		   unsigned int width)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, width, value));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, width, num, value);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   tUInt32 value,
		   unsigned int width)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, width, value));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, width, num, value);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   tUInt64 value,
		   unsigned int width)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, width, value));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, width, num, value);
  }
}

void vcd_write_val(tSimStateHdl simHdl,
		   unsigned int num,
		   const tUWide& value,
		   unsigned int width)
{
  tTime time = time_of_change(simHdl, num);
  if (time > (simHdl->vcd).min_pending)
    (simHdl->vcd).changes[time].push_back(Change(num, value));
  else
  {
    vcd_output_at_time(simHdl, time);
    print_change(simHdl, width, num, value);
  }
}


// The VCD format elides leading zeros
static void print_binary(Target* dest, unsigned int width, tUInt64 value)
{  
  bool leading_zero = true;
  while (width-- > 0)
  {
    if ((value >> width) & 0x1llu)
    {
      dest->write_char('1');
      leading_zero = false;
    }
    else if (!leading_zero)
    {
      dest->write_char('0');
    }
  }

  if (leading_zero)
  {
    // there were no non-zero bits at all!
    dest->write_char('0');    
  }
}

static void print_X(tSimStateHdl simHdl, unsigned int bits, unsigned int num)
{
  FileTarget dest((simHdl->vcd).vcd_file);
  if (bits == 1)
    dest.write_char('x');
  else
    dest.write_string("bx ");
  vcd_write_id(simHdl, num);
  dest.write_char('\n');  
}

static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, tUInt64 val)
{
  FileTarget dest((simHdl->vcd).vcd_file);
  if (bits == 1)
    dest.write_char(val ? '1' : '0');
  else
  {
    dest.write_char('b');
    print_binary(&dest, bits, val);
    dest.write_char(' ');
  }
  vcd_write_id(simHdl, num);
  dest.write_char('\n');  
}

static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, const tUWide& val)
{
  FileTarget dest((simHdl->vcd).vcd_file);
  if (bits == 1)
    val.print_binary(&dest);
  else
  {
    dest.write_char('b');
    val.print_binary(&dest);
    dest.write_char(' ');
  }
  vcd_write_id(simHdl, num);
  dest.write_char('\n');  
}
