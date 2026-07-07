#include <time.h>
#include <cstdio>
#include <cstring>
#include <string>

#include "bluesim_kernel_api.h"
#include "kernel.h"
#include "bs_vcd.h"
#include "bs_wave_writer.h"
#include "bs_target.h"

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
 * can assign a change to that time have occurred, at which point
 * changes for that time are written to the VCD file.
 *
 * This engine is format-independent; the bytes are produced by a
 * WaveWriter (the VCD text writer below, or the FST writer in
 * fst.cxx).  Which formats are available in a given model is
 * recorded by generated code via vcd_set_allowed_formats() and
 * vcd_register_fst(), and the format in use is selected with
 * bk_set_waveform_format().
 */

/*
 * The VCD text writer
 */

class VcdWriter : public WaveWriter
{
private:
  FILE* file;
  std::string file_name;
  tUInt64 size_limit;

  void put_id(unsigned int num)
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
    FileTarget dest(file);
    dest.write_data(cptr,sizeof(char),len);
  }

  // The VCD format elides leading zeros
  void put_binary(Target* dest, unsigned int width, tUInt64 value)
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

public:
  VcdWriter() : file(NULL), size_limit(0llu) {}
  ~VcdWriter() { if (file != NULL) fclose(file); }

  bool open(const char* name, bool append)
  {
    // if we are returning to a previous file, append to it
    file = fopen(name, append ? "a" : "w");
    if (file == NULL)
    {
      perror(name);
      return false;
    }
    file_name = name;
    return true;
  }

  void close()
  {
    if (file != NULL)
      fclose(file);
    file = NULL;
  }

  void flush()
  {
    if (file != NULL)
      fflush(file);
  }

  void write_header(const char* timescale)
  {
    FileTarget dest(file);

    time_t t = time(NULL);
    dest.write_string("$date\n\t%s$end\n", ctime(&t));
    dest.write_string("$version\n");
    dest.write_string("\tBluespec VCD dumper %d.%d\n",
                      bs_wave_major_rev, bs_wave_minor_rev);
    dest.write_string("$end\n");
    dest.write_string("$timescale\n\t%s\n$end\n", timescale);
  }

  void start_scope(const char* name, const char* /* no place in VCD */)
  {
    fprintf(file, "$scope module %s $end\n", name);
  }

  void end_scope()
  {
    fprintf(file, "$upscope $end\n");
  }

  void write_def(unsigned int num, const char* name, unsigned int width)
  {
    FileTarget dest(file);
    dest.write_string("$var reg %d ", width);
    put_id(num);
    dest.write_string(" %s $end\n", name);
  }

  void end_definitions()
  {
    fputs("$enddefinitions $end\n", file);
  }

  void finish_task_block()
  {
    FileTarget dest(file);
    dest.write_string("$end\n");
  }

  void write_time(tTime time)
  {
    FileTarget dest(file);
    dest.write_string("#%llu\n", time);
  }

  void start_task_block(const char* task)
  {
    FileTarget dest(file);
    dest.write_string("%s\n", task);
  }

  void write_x(unsigned int num, unsigned int bits)
  {
    FileTarget dest(file);
    if (bits == 1)
      dest.write_char('x');
    else
      dest.write_string("bx ");
    put_id(num);
    dest.write_char('\n');
  }

  void write_change(unsigned int num, unsigned int bits, tUInt64 value)
  {
    FileTarget dest(file);
    if (bits == 1)
      dest.write_char(value ? '1' : '0');
    else
    {
      dest.write_char('b');
      put_binary(&dest, bits, value);
      dest.write_char(' ');
    }
    put_id(num);
    dest.write_char('\n');
  }

  void write_change(unsigned int num, unsigned int bits, const tUWide& value)
  {
    FileTarget dest(file);
    if (bits == 1)
      value.print_binary(&dest);
    else
    {
      dest.write_char('b');
      value.print_binary(&dest);
      dest.write_char(' ');
    }
    put_id(num);
    dest.write_char('\n');
  }

  void write_comment(const char* comment)
  {
    FileTarget dest(file);
    dest.write_string("$comment\n%s$end\n", comment);
  }

  void write_id(unsigned int num)
  {
    put_id(num);
  }

  void set_size_limit(tUInt64 bytes)
  {
    size_limit = bytes;
  }

  bool limit_exceeded()
  {
    if ((file == NULL) || (size_limit == 0llu))
      return false;
    unsigned long long sz = (unsigned long long) ftello(file);
    return (sz > size_limit);
  }
};

static WaveWriter* new_vcd_writer()
{
  return new VcdWriter;
}

// forward declarations
static void flush_changes(tSimStateHdl simHdl);
static void print_X(tSimStateHdl simHdl, unsigned int bits, unsigned int num);
static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, tUInt64 val);
static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, const tUWide& val);

/*
 * Format bookkeeping
 */

// Called by generated model code to record which formats this model
// was built with (-dump-formats).  Also selects the default format.
void vcd_set_allowed_formats(tSimStateHdl simHdl, unsigned int formats)
{
  tVCDState* s = &(simHdl->vcd);
  s->allowed_formats = formats;
  if (formats & BS_WAVE_FORMAT_VCD)
    s->format = BS_WAVE_FORMAT_VCD;
  else if (formats & BS_WAVE_FORMAT_FST)
    s->format = BS_WAVE_FORMAT_FST;
}

// Test whether the current format was compiled into this model,
// reporting an error if it was not.
static bool vcd_format_available(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);
  if (s->allowed_formats == 0u)
  {
    fprintf(stderr, "Error: this model was built with -dump-formats none; "
                    "no waveform dumping is available\n");
    return false;
  }
  if ((s->allowed_formats & s->format) == 0u)
  {
    const char* name = (s->format == BS_WAVE_FORMAT_FST) ? "FST" : "VCD";
    const char* flag = (s->format == BS_WAVE_FORMAT_FST) ? "fst" : "vcd";
    fprintf(stderr, "Error: this model was not built with %s support "
                    "(rebuild with -dump-formats %s)\n", name, flag);
    return false;
  }
  return true;
}

// Construct the writer for the current format
static WaveWriter* new_writer(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);
  if (s->format == BS_WAVE_FORMAT_FST)
  {
    if (s->fst_writer_factory != NULL)
      return s->fst_writer_factory();
    // should be unreachable: the format is gated on the allowed set,
    // and models built with fst register the factory
    fprintf(stderr, "Error: no FST writer is linked into this model\n");
    return NULL;
  }
  return new_vcd_writer();
}

static const char* format_name(unsigned int format)
{
  return (format == BS_WAVE_FORMAT_FST) ? "fst" : "vcd";
}

static const char* default_file_name(tSimStateHdl simHdl)
{
  return ((simHdl->vcd).format == BS_WAVE_FORMAT_FST) ? "dump.fst"
                                                      : "dump.vcd";
}

tStatus bk_set_waveform_format(tSimStateHdl simHdl, const char* format)
{
  tVCDState* s = &(simHdl->vcd);

  unsigned int fmt;
  if (format != NULL && !strcmp(format, "vcd"))
    fmt = BS_WAVE_FORMAT_VCD;
  else if (format != NULL && !strcmp(format, "fst"))
    fmt = BS_WAVE_FORMAT_FST;
  else
  {
    fprintf(stderr, "Error: unknown waveform format '%s' "
                    "(supported: vcd, fst)\n",
            (format == NULL) ? "" : format);
    return BK_ERROR;
  }

  if (s->allowed_formats == 0u)
  {
    fprintf(stderr, "Error: this model was built with -dump-formats none; "
                    "no waveform dumping is available\n");
    return BK_ERROR;
  }
  if ((s->allowed_formats & fmt) == 0u)
  {
    fprintf(stderr, "Error: this model was not built with %s support "
                    "(rebuild with -dump-formats %s)\n",
            (fmt == BS_WAVE_FORMAT_FST) ? "FST" : "VCD",
            format_name(fmt));
    return BK_ERROR;
  }

  if (fmt == s->format)
    return BK_SUCCESS;

  // Switching formats ends any dump in progress: buffered changes are
  // flushed to the open file, dumping is disabled and the file is
  // closed.  Dumping can then be (re)enabled to a file of the new
  // format.
  if (s->vcd_enabled)
    bk_disable_VCD_dumping(simHdl);
  // no final all-X dump or checkpoint: the file is closing
  s->go_xs = false;
  s->vcd_checkpoint = false;
  if (s->writer != NULL)
  {
    // flush buffered changes to the closing file
    s->changes_now = false;
    s->min_pending = bk_now(simHdl);
    flush_changes(simHdl);
    if (s->need_end_task)
    {
      s->writer->finish_task_block();
      s->need_end_task = false;
    }
  }
  s->changes.clear();
  s->tasks.clear();
  bk_set_VCD_file(simHdl, NULL);
  s->format = fmt;

  return BK_SUCCESS;
}

const char* bk_get_waveform_format(tSimStateHdl simHdl)
{
  return format_name((simHdl->vcd).format);
}

tStatus bk_set_VCD_file(tSimStateHdl simHdl, const char* name)
{
  tVCDState* s = &(simHdl->vcd);

  if (s->writer != NULL)
  {
    s->writer->close();
    delete s->writer;
    s->writer = NULL;
  }
  s->vcd_file_name.resize(0);

  s->state = VCD_OFF;
  if (name == NULL)
    return BK_SUCCESS;

  if (!vcd_format_available(simHdl))
    return BK_ERROR;

  s->vcd_file_name = name;
  // if we are returning to a previous file, do not write the header again
  bool append = (s->previous_files.find(s->vcd_file_name) !=
                 s->previous_files.end());

  s->writer = new_writer(simHdl);
  if ((s->writer == NULL) || !s->writer->open(name, append))
  {
    delete s->writer;
    s->writer = NULL;
    s->vcd_file_name.resize(0);
    return BK_ERROR;
  }

  if (append)
    s->state = VCD_DISABLED;
  s->writer->set_size_limit(s->vcd_filesize_limit);

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
  if ((simHdl->vcd).writer == NULL)
  {
    if (bk_set_VCD_file(simHdl, default_file_name(simHdl)) != BK_SUCCESS)
      return BK_ERROR;
  }

  (simHdl->vcd).vcd_checkpoint = true;

  return BK_SUCCESS;
}

void bk_set_VCD_filesize_limit(tSimStateHdl simHdl, tUInt64 bytes)
{
  (simHdl->vcd).vcd_filesize_limit = bytes;
  if ((simHdl->vcd).writer != NULL)
    (simHdl->vcd).writer->set_size_limit(bytes);
}

void bk_flush_VCD_output(tSimStateHdl simHdl)
{
  if ((simHdl->vcd).writer != NULL)
    (simHdl->vcd).writer->flush();
}

/* VCD routines used by the simulation kernel */

void vcd_reset(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);

  s->changes_now = false;
  s->min_pending = bk_now(simHdl);
  flush_changes(simHdl);
  if (s->writer != NULL)
  {
    s->writer->close();
    delete s->writer;
    s->writer = NULL;
  }
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
  if (enabled && ((simHdl->vcd).writer == NULL))
  {
    if (bk_set_VCD_file(simHdl, default_file_name(simHdl)) != BK_SUCCESS)
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

  if (s->writer == NULL)
    return false;

  if (s->state != VCD_OFF)
    return false;

  s->state = VCD_HEADER;

  s->writer->write_header(s->vcd_timescale);

  s->next_seq_num = s->kept_seq_num;

  return true;
}

bool vcd_check_file_size(tSimStateHdl simHdl)
{
  tVCDState* s = &(simHdl->vcd);
  if ((s->writer != NULL) && (s->vcd_filesize_limit != 0llu))
  {
    if (s->writer->limit_exceeded())
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
  if ((simHdl->vcd).writer != NULL)
    (simHdl->vcd).writer->write_comment(comment);
}

void vcd_set_backing_instance(tSimStateHdl simHdl, bool b)
{
  (simHdl->vcd).is_backing_instance = b;
}

void vcd_end_definitions(tSimStateHdl simHdl)
{
  if ((simHdl->vcd).writer != NULL)
    (simHdl->vcd).writer->end_definitions();
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
  if ((simHdl->vcd).writer != NULL)
    (simHdl->vcd).writer->write_id(num);
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
    (simHdl->vcd).writer->write_def(num, s, 1);
}

void vcd_set_clock(tSimStateHdl simHdl, unsigned int num, tClock handle)
{
  if (handle == BAD_CLOCK_HANDLE)
    return;

  (simHdl->vcd).clk_map.insert(std::make_pair(num,handle));
}

void vcd_write_scope_start(tSimStateHdl simHdl, const char* name)
{
  (simHdl->vcd).writer->start_scope(name, NULL);
}

void vcd_write_scope_start(tSimStateHdl simHdl,
			   const char* name, const char* module_type)
{
  (simHdl->vcd).writer->start_scope(name, module_type);
}

void vcd_write_scope_end(tSimStateHdl simHdl)
{
  (simHdl->vcd).writer->end_scope();
}

void vcd_write_def(tSimStateHdl simHdl,
		   unsigned int num,
		   const char* name,
		   unsigned int width)
{
  (simHdl->vcd).writer->write_def(num, name, width);
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
  if ((simHdl->vcd).writer == NULL)
  {
    // no open file to write to; drop anything pending
    (simHdl->vcd).changes.clear();
    return;
  }

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

  WaveWriter* writer = (simHdl->vcd).writer;

  if ((simHdl->vcd).need_end_task)
    writer->finish_task_block();

  writer->write_time(time);

  /* If there is a task name associated with this time, print it */
  std::map<tTime, const char*>::iterator p = (simHdl->vcd).tasks.find(time);
  if (p != (simHdl->vcd).tasks.end())
  {
    (simHdl->vcd).need_end_task = true;
    writer->start_task_block(p->second);
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


static void print_X(tSimStateHdl simHdl, unsigned int bits, unsigned int num)
{
  (simHdl->vcd).writer->write_x(num, bits);
}

static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, tUInt64 val)
{
  (simHdl->vcd).writer->write_change(num, bits, val);
}

static void print_change(tSimStateHdl simHdl,
			 unsigned int bits, unsigned int num, const tUWide& val)
{
  (simHdl->vcd).writer->write_change(num, bits, val);
}
