/* FST waveform writer for Bluesim.
 *
 * This implements the WaveWriter interface (see bs_wave_writer.h) on
 * top of GTKWave's libfst (the src/vendor/libfst submodule).  The dump
 * engine in vcd.cxx does all of the policy work; this file only
 * translates definitions, times and value changes into fstWriter calls.
 *
 * Models are linked against this writer only when they are built with
 * -dump-formats fst: the generated model code calls vcd_register_fst(),
 * and that reference is what pulls this object (and the fstapi objects
 * it uses, plus their libz dependency) out of the kernel library.
 */

#include <cstdio>
#include <cstring>
#include <vector>

#include "bluesim_kernel_api.h"
#include "kernel.h"
#include "bs_vcd.h"
#include "bs_wave_writer.h"

#include "fstapi.h"

class FstWriter : public WaveWriter
{
private:
  fstWriterContext* ctx;
  // per-num signal info, indexed by the engine's id numbers
  std::vector<fstHandle> handles;
  std::vector<unsigned int> widths;
  // FST times must be monotonically non-decreasing
  tTime last_time;
  bool wrote_time;
  // scratch buffer for char-per-bit value changes
  std::vector<char> buf;
  // File-size limiting.  fstapi has its own dump-size limit, but it
  // is only checked when a section is flushed (every ~128MB of
  // buffered change data), far too coarse for Bluesim's per-event
  // limit checks.  Instead, estimate the size the equivalent VCD
  // text would have (matching its leading-zero elision), so that a
  // $dumplimit stops an FST dump at the same point in the simulation
  // where it would stop a VCD dump.
  tUInt64 size_limit;
  tUInt64 bytes_emitted;

  // significant_bits digits (at least one), the 'b'/' ' framing for
  // vectors, and roughly an id code plus a newline
  void count_change(unsigned int width, unsigned int significant_bits)
  {
    unsigned int digits = (significant_bits > 0) ? significant_bits : 1;
    bytes_emitted += ((width == 1) ? 1 : (digits + 2)) + 4;
  }

  // fstWriterEmitValueChange requires exactly the declared number of
  // bits, so changes are padded (or truncated) to the declared width.
  unsigned int width_of(unsigned int num)
  {
    if ((num < widths.size()) && (widths[num] != 0))
      return widths[num];
    return 1;
  }

  bool has_handle(unsigned int num)
  {
    return (ctx != NULL) && (num < handles.size()) && (handles[num] != 0);
  }

public:
  FstWriter()
    : ctx(NULL), last_time(0llu), wrote_time(false),
      size_limit(0llu), bytes_emitted(0llu)
  {}

  ~FstWriter() { close(); }

  bool open(const char* name, bool /* append: FST files are one-shot */)
  {
    ctx = fstWriterCreate(name, 1 /* compressed hierarchy */);
    if (ctx == NULL)
    {
      perror(name);
      return false;
    }
    fstWriterSetPackType(ctx, FST_WR_PT_LZ4);
    return true;
  }

  void close()
  {
    if (ctx != NULL)
      fstWriterClose(ctx);
    ctx = NULL;
  }

  void flush()
  {
    if (ctx != NULL)
      fstWriterFlushContext(ctx);
  }

  void write_header(const char* timescale)
  {
    char version[64];
    snprintf(version, sizeof(version), "Bluespec FST dumper %d.%d",
             bs_wave_major_rev, bs_wave_minor_rev);
    fstWriterSetVersion(ctx, version);
    fstWriterSetTimescaleFromString(ctx, timescale);

    // when a header is (re)written the engine hands out ids afresh
    handles.clear();
    widths.clear();

    // the equivalent of VCD's $date/$version/$timescale text
    bytes_emitted += 120;
  }

  void start_scope(const char* name, const char* module_type)
  {
    // the module type is recorded as the scope's component name,
    // where viewers (and fstReaderIterateHier) can retrieve it
    fstWriterSetScope(ctx, FST_ST_VCD_MODULE, name, module_type);
    bytes_emitted += strlen(name) + 22;  // "$scope module ... $end"
  }

  void end_scope()
  {
    fstWriterSetUpscope(ctx);
    bytes_emitted += 15;  // "$upscope $end"
  }

  void write_def(unsigned int num, const char* name, unsigned int width)
  {
    if (num >= handles.size())
    {
      handles.resize(num + 1, 0);
      widths.resize(num + 1, 0);
    }
    if (handles[num] != 0)
    {
      // an additional definition of the same id is an alias
      fstWriterCreateVar(ctx, FST_VT_VCD_REG, FST_VD_IMPLICIT,
                         widths[num], name, handles[num]);
      return;
    }
    if (width == 0)
      width = 1;
    handles[num] = fstWriterCreateVar(ctx, FST_VT_VCD_REG, FST_VD_IMPLICIT,
                                      width, name, 0);
    widths[num] = width;
    bytes_emitted += strlen(name) + 18;  // "$var reg N ! ... $end"
  }

  void end_definitions() {}

  void finish_task_block() {}

  void write_time(tTime time)
  {
    // guard against any non-monotonic residue in the change buffering
    if (wrote_time && (time < last_time))
      time = last_time;
    fstWriterEmitTimeChange(ctx, time);
    last_time = time;
    wrote_time = true;
    bytes_emitted += 8;
  }

  void start_task_block(const char* task)
  {
    // $dumpvars/$dumpall carry no extra information in FST (the values
    // themselves are dumped); $dumpoff/$dumpon map to blackout regions
    if (!strcmp(task, "$dumpoff"))
      fstWriterEmitDumpActive(ctx, 0);
    else if (!strcmp(task, "$dumpon"))
      fstWriterEmitDumpActive(ctx, 1);
  }

  void write_x(unsigned int num, unsigned int /* bits */)
  {
    if (!has_handle(num))
      return;
    unsigned int w = width_of(num);
    buf.assign(w, 'x');
    fstWriterEmitValueChange(ctx, handles[num], &buf[0]);
    count_change(w, 1);
  }

  void write_change(unsigned int num, unsigned int /* bits */, tUInt64 value)
  {
    if (!has_handle(num))
      return;
    unsigned int w = width_of(num);
    if (w <= 32)
      fstWriterEmitValueChange32(ctx, handles[num], w, (tUInt32) value);
    else if (w <= 64)
      fstWriterEmitValueChange64(ctx, handles[num], w, value);
    else
    {
      // declared wider than the 64-bit value: pad with leading zeros
      buf.assign(w, '0');
      for (unsigned int i = 0; (i < 64) && (i < w); ++i)
        buf[w - 1 - i] = '0' + (char)((value >> i) & 0x1llu);
      fstWriterEmitValueChange(ctx, handles[num], &buf[0]);
    }
    unsigned int sig = 0;
    for (tUInt64 v = value; v != 0llu; v >>= 1)
      ++sig;
    count_change(w, sig);
  }

  void write_change(unsigned int num, unsigned int /* bits */,
                    const tUWide& value)
  {
    if (!has_handle(num))
      return;
    unsigned int w = width_of(num);
    unsigned int nbits = value.size();
    buf.assign(w, '0');
    unsigned int sig = 0;
    for (unsigned int i = 0; (i < nbits) && (i < w); ++i)
    {
      unsigned int bit = (value[i >> 5] >> (i & 31)) & 0x1u;
      buf[w - 1 - i] = '0' + (char)bit;
      if (bit)
        sig = i + 1;
    }
    fstWriterEmitValueChange(ctx, handles[num], &buf[0]);
    count_change(w, sig);
  }

  void write_comment(const char* /* comment */)
  {
    // The engine's only comment today is the file-size-limit message,
    // which the VCD writer records inside the file.  There is no safe
    // in-file place for it in FST (fstWriterSetComment writes an
    // attribute that widespread older FST readers, e.g. GTKWave 3.3's
    // fst2vcd, reject as malformed), and printing it would make
    // dumping change the simulation's observable output -- which the
    // testsuite checks it never does -- so a tripped limit just stops
    // the dump, and the file ends at the limit.
  }

  void set_size_limit(tUInt64 bytes)
  {
    size_limit = bytes;
  }

  bool limit_exceeded()
  {
    return (size_limit != 0llu) && (bytes_emitted > size_limit);
  }
};

static WaveWriter* new_fst_writer()
{
  return new FstWriter;
}

// Called by generated model code (when built with -dump-formats fst)
// to make the FST writer available for format selection.
void vcd_register_fst(tSimStateHdl simHdl)
{
  (simHdl->vcd).fst_writer_factory = new_fst_writer;
}
