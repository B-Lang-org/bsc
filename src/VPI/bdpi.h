#ifndef __BDPI_H__
#define __BDPI_H__

#include "vpi_user.h"

typedef enum { DIRECT, POLYMORPHIC, STRING } tPtrType;

/* allocate storage for a result, if needed */
void make_vpi_result(vpiHandle hdl, void* ptr, tPtrType type);

/* copy a value from the Verilog side, allocating storage if required */
void get_vpi_arg(vpiHandle hdl, void* ptr, tPtrType type);

/* copy a return value back to the Verilog side and free the storage */
void put_vpi_result(vpiHandle hdl, void* ptr, tPtrType type);

/* free all storage allocated by get_vpi_arg() */
void free_vpi_args(void);

#endif /* __BDPI_H__ */
