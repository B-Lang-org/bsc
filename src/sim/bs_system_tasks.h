#ifndef __BS_SYSTEM_TASKS_H__
#define __BS_SYSTEM_TASKS_H__

#include <string>
#include "bluesim_types.h"
class Module; // forward declaration

/*
 * Declarations of Verilog system tasks
 */

// stop & finish
extern void dollar_stop(tSimStateHdl simHdl,
			const char* size_str="", int status = 0);
extern void dollar_finish(tSimStateHdl simHdl,
			  const char* size_str="", int status = 0);

// display system tasks
extern void dollar_display(tSimStateHdl simHdl, Module* location,
			   const char* size_str ...);
extern void dollar_display(tSimStateHdl simHdl, Module* location);
extern void dollar_displayb(tSimStateHdl simHdl, Module* location,
			    const char* size_str ...);
extern void dollar_displayb(tSimStateHdl simHdl, Module* location);
extern void dollar_displayo(tSimStateHdl simHdl, Module* location,
			    const char* size_str ...);
extern void dollar_displayo(tSimStateHdl simHdl, Module* location);
extern void dollar_displayh(tSimStateHdl simHdl, Module* location,
			    const char* size_str ...);
extern void dollar_displayh(tSimStateHdl simHdl, Module* location);

// write system tasks
extern void dollar_write(tSimStateHdl simHdl, Module* location,
			 const char* size_str ...);
extern void dollar_write(tSimStateHdl simHdl, Module* location);
extern void dollar_writeb(tSimStateHdl simHdl, Module* location,
			  const char* size_str ...);
extern void dollar_writeb(tSimStateHdl simHdl, Module* location);
extern void dollar_writeo(tSimStateHdl simHdl, Module* location,
			  const char* size_str ...);
extern void dollar_writeo(tSimStateHdl simHdl, Module* location);
extern void dollar_writeh(tSimStateHdl simHdl, Module* location,
			  const char* size_str ...);
extern void dollar_writeh(tSimStateHdl simHdl, Module* location);

// File operations
extern tUInt32 dollar_fopen(const char* size_str, const std::string* filename,
			                          const std::string* mode);
extern tUInt32 dollar_fopen(const char* size_str, const std::string* filename);

extern void dollar_fclose(const char* size_str,const tUInt32 filehandle);
extern void dollar_fflush();
extern void dollar_fflush(const char* size_str, const tUInt32 filehandle);

extern tSInt32 dollar_fgetc(  const char* size_str, const tUInt32 filehandle ) ;
extern tSInt32 dollar_ungetc( const char* size_str, const char, const tUInt32 filehandle ) ;

// fdisplay system tasks
extern void dollar_fdisplay(tSimStateHdl simHdl, Module* location,
			    const char* size_str ...);
extern void dollar_fdisplayb(tSimStateHdl simHdl, Module* location,
			     const char* size_str ...);
extern void dollar_fdisplayo(tSimStateHdl simHdl, Module* location,
			     const char* size_str ...);
extern void dollar_fdisplayh(tSimStateHdl simHdl, Module* location,
			     const char* size_str ...);

// fwrite system tasks
extern void dollar_fwrite(tSimStateHdl simHdl, Module* location,
			  const char* size_str ...);
extern void dollar_fwriteb(tSimStateHdl simHdl, Module* location,
			   const char* size_str ...);
extern void dollar_fwriteo(tSimStateHdl simHdl, Module* location,
			   const char* size_str ...);
extern void dollar_fwriteh(tSimStateHdl simHdl, Module* location,
			   const char* size_str ...);

// sformat and swrite system tasks
extern void dollar_sformatAV(tSimStateHdl simHdl, Module* location,
			     const char* size_str, ...);
extern void dollar_swriteAV(tSimStateHdl simHdl, Module* location,
			    const char* size_str, ...);
extern void dollar_swritebAV(tSimStateHdl simHdl, Module* location,
			     const char* size_str, ...);
extern void dollar_swriteoAV(tSimStateHdl simHdl, Module* location,
			     const char* size_str, ...);
extern void dollar_swritehAV(tSimStateHdl simHdl, Module* location,
			     const char* size_str, ...);

// error, warning, etc.
extern void dollar_info(tSimStateHdl simHdl, Module* location,
			const char* size_str, ...);
extern void dollar_info(tSimStateHdl simHdl, Module* location);
extern void dollar_warning(tSimStateHdl simHdl, Module* location,
			   const char* size_str, ...);
extern void dollar_warning(tSimStateHdl simHdl, Module* location);
extern void dollar_error(tSimStateHdl simHdl, Module* location,
			 const char* size_str, ...);
extern void dollar_error(tSimStateHdl simHdl, Module* location);
extern void dollar_fatal(tSimStateHdl simHdl, Module* location,
			 const char* size_str, ...);

// simulation time system tasks
extern tUInt64 dollar_time(tSimStateHdl simHdl);
extern tUInt32 dollar_stime(tSimStateHdl simHdl);

// plusargs tasks
extern bool dollar_test_dollar_plusargs(tSimStateHdl simHdl,
					const char* size_str,
					const std::string* name);

// VCD-related tasks
extern void dollar_dumpfile(tSimStateHdl simHdl);
extern void dollar_dumpfile(tSimStateHdl simHdl,
			    const char* size_str,
			    const std::string* name);
extern void dollar_dumpvars(tSimStateHdl simHdl,
			    const char* size_str = NULL,
			    unsigned int depth = 0);
extern void dollar_dumpon(tSimStateHdl simHdl);
extern void dollar_dumpoff(tSimStateHdl simHdl);
extern void dollar_dumpall(tSimStateHdl simHdl);
extern void dollar_dumplimit(tSimStateHdl simHdl,
			     const char* size_str,
			     unsigned long long bytes);
extern void dollar_dumpflush(tSimStateHdl simHdl);

#endif /* __BS_SYSTEM_TASKS_H__ */
