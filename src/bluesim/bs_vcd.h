#ifndef __BS_VCD_H__
#define __BS_VCD_H__

/* The VCD functionality declared in this header file
 * is internal, C++ functionality.  The external VCD interface
 * is declared in the bluesim_kernel_api.h file.
 */
#include <cstdio>
#include <list>
#include <set>
#include <map>
#include "bluesim_types.h"
#include "bs_wide_data.h"
#include "bs_module.h"

typedef enum { VCD_DUMP_NONE
	     , VCD_DUMP_XS
	     , VCD_DUMP_INITIAL
	     , VCD_DUMP_CHECKPOINT
	     , VCD_DUMP_CHANGES
	     , VCD_DUMP_RESTART
             } tVCDDumpType;

/* used by the kernel and schedule */

extern void vcd_reset(tSimStateHdl simHdl);
extern void vcd_dump_xs(tSimStateHdl simHdl);
extern bool vcd_set_state(tSimStateHdl simHdl, bool enabled);
extern bool vcd_is_active(tSimStateHdl simHdl);
extern void vcd_keep_ids(tSimStateHdl simHdl);
extern void vcd_write_comment(tSimStateHdl simHdl, const char* comment);
extern bool vcd_write_header(tSimStateHdl simHdl);
extern tVCDDumpType get_VCD_dump_type(tSimStateHdl simHdl);
extern bool vcd_check_file_size(tSimStateHdl simHdl);
extern void vcd_set_backing_instance(tSimStateHdl simHdl, bool b);

extern void vcd_task(tSimStateHdl simHdl, const char* task);

/* used by modules */
extern tUInt32 vcd_depth(tSimStateHdl simHdl);
extern bool vcd_is_backing_instance(tSimStateHdl simHdl);
extern unsigned int vcd_reserve_ids(tSimStateHdl simHdl, unsigned int num);
extern void vcd_add_clock_def(tSimStateHdl simHdl,
			      Module* module, const char* s, unsigned int num);
extern void vcd_write_id(tSimStateHdl simHdl, unsigned int num);
extern void vcd_set_clock(tSimStateHdl simHdl,
			  unsigned int num, tClock handle);
extern void vcd_write_scope_start(tSimStateHdl simHdl, const char* name);
extern void vcd_write_scope_end(tSimStateHdl simHdl);
extern void vcd_write_def(tSimStateHdl simHdl,
			  unsigned int num,
			  const char* name,
			  unsigned int width);
extern void vcd_advance(tSimStateHdl simHdl, bool immediate);
extern void vcd_output_at_time(tSimStateHdl simHdl, tTime time);
extern void vcd_write_x(tSimStateHdl simHdl,
			unsigned int num,
			unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  tClockValue value,
			  unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  bool value,
			  unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  tUInt8 value,
			  unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  tUInt32 value,
			  unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  tUInt64 value,
			  unsigned int width);
extern void vcd_write_val(tSimStateHdl simHdl,
			  unsigned int num,
			  const tUWide& value,
			  unsigned int width);

#endif /* __BS_VCD_H__ */

