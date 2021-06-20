#ifndef __BS_MODEL_H__
#define __BS_MODEL_H__

#include "bluesim_types.h"
#include "bs_vcd.h"

/* This is the (pure virtual) base class for Bluesim-generated designs.
 * It declares the functions that the kernel requires from a design.
 */

class Model
{
 // The functions that the kernel requires, declared as pure virtual
 // functions so that derived classes have to define them.
 public:
  virtual void create_model(tSimStateHdl simHdl, bool master) = 0;
  virtual void destroy_model() = 0;
  virtual void reset_model(bool asserted) = 0;
  virtual void get_version(char const **name, char const **build) = 0;
  virtual time_t get_creation_time() = 0;
  virtual void * get_instance() = 0;
  virtual void dump_state() = 0;
  virtual void dump_VCD_defs() = 0;
  virtual void dump_VCD(tVCDDumpType dt) = 0;

 // Require construction be of the derived classes, not this class
 protected:
  Model() { };

 // Similarly, prevent use of the copy constructor and the assignment operator
 private:
  Model(Model const & m) { };
  Model & operator= (Model const & m) { return *this; };

 // Declare the destructor as virtual, so that the derived destructor is used
 public:
  virtual ~Model() { };
};

#endif /* __BS_MODEL_H__ */
