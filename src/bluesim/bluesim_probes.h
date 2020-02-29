#ifndef __BLUESIM_PROBES_H__
#define __BLUESIM_PROBES_H__

#include "bs_wide_data.h"

/*
 * Definition of the BluespecProbe type used to access the
 * internal state of a Bluesim model.
 */

template<typename DATAT, typename ADDRT = unsigned int>
class BluespecProbe
{
  typedef ADDRT        (*tBoundFn)(void*, bool);
  typedef bool         (*tAddrFn)(void*, ADDRT);
  typedef const DATAT& (*tReadFn)(void*, ADDRT);
  typedef bool         (*tWriteFn)(void*, ADDRT, const DATAT&);

 public:
  BluespecProbe(void* el, tBoundFn bound_fn, tAddrFn addr_fn,
                tReadFn read_fn, tWriteFn write_fn)
   : element(el), get_bound(bound_fn), test_addr(addr_fn),
     do_read(read_fn), do_write(write_fn)
  {
  }
   
  ADDRT low_address()  const { return get_bound(element, false); }
  ADDRT high_address() const { return get_bound(element, true); }
  bool is_valid_address(const ADDRT& addr) const
  {
    return test_addr(element, addr);
  }
  const DATAT& read(const ADDRT& addr) const
  {
    return do_read(element, addr);
  }
  bool write(const ADDRT& addr, const DATAT& data)
  {
    return do_write(element, addr, data);
  }
  const DATAT& read() const     { return read(low_address()); }
  bool write(const DATAT& data) { return write(low_address(), data); }

 private:
  void* element;
  ADDRT (*get_bound)(void* obj, bool hi);
  bool (*test_addr)(void* obj, ADDRT addr);
  const DATAT& (*do_read)(void* obj, ADDRT addr);
  bool (*do_write)(void* obj, ADDRT addr, const DATAT& data);
};

#endif /* __BLUESIM_PROBES_H__ */
