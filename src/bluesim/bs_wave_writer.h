#ifndef __BS_WAVE_WRITER_H__
#define __BS_WAVE_WRITER_H__

/* Internal interface between the waveform-dump engine (vcd.cxx) and
 * the format-specific writers (the VCD writer in vcd.cxx and the FST
 * writer in fst.cxx).
 *
 * The engine owns all of the dump policy: id allocation, association
 * of signals with clocks, buffering of changes until their corrected
 * times are final, the $dump* task bookkeeping and the dump-type state
 * machine.  A WaveWriter only turns the resulting stream of headers,
 * definitions, times and value changes into bytes in some file format.
 */

#include "bluesim_types.h"
#include "bs_wide_data.h"

// Waveform dumper version, shared by all formats
static const unsigned int bs_wave_major_rev = 2;
static const unsigned int bs_wave_minor_rev = 1;

class WaveWriter
{
public:
  virtual ~WaveWriter() {}

  // File management.  open() reports errors itself (on stderr) and
  // returns false.  When "append" is true the file was already dumped
  // to earlier in this simulation and is being resumed.
  virtual bool open(const char* name, bool append) = 0;
  virtual void close() = 0;
  virtual void flush() = 0;

  // Header and signal definitions.  A scope's module_type (the name
  // of the module the scope is an instance of) may be NULL when it
  // is not known; formats without a place for it ignore it.
  virtual void write_header(const char* timescale) = 0;
  virtual void start_scope(const char* name, const char* module_type) = 0;
  virtual void end_scope() = 0;
  // Defining the same num again creates an alias of the earlier signal
  virtual void write_def(unsigned int num,
                         const char* name,
                         unsigned int width) = 0;
  virtual void end_definitions() = 0;

  // Time stamps and $dump* task markers.  Calls arrive in the order:
  // finish_task_block (if a task block was left open), write_time,
  // then optionally start_task_block for a task at the new time.
  virtual void finish_task_block() = 0;
  virtual void write_time(tTime time) = 0;
  virtual void start_task_block(const char* task) = 0;

  // Value changes (already time-corrected and ordered by the engine)
  virtual void write_x(unsigned int num, unsigned int bits) = 0;
  virtual void write_change(unsigned int num,
                            unsigned int bits,
                            tUInt64 value) = 0;
  virtual void write_change(unsigned int num,
                            unsigned int bits,
                            const tUWide& value) = 0;

  virtual void write_comment(const char* comment) = 0;

  // Write just the id code for a signal number (only meaningful for
  // formats with textual id codes; exposed for vcd_write_id compatibility)
  virtual void write_id(unsigned int num) {}

  // File-size limiting; a limit of 0 means unlimited
  virtual void set_size_limit(tUInt64 bytes) = 0;
  virtual bool limit_exceeded() = 0;
};

// Factory used to construct a writer for a registered format
typedef WaveWriter* (*tWaveWriterFactory)();

#endif /* __BS_WAVE_WRITER_H__ */
