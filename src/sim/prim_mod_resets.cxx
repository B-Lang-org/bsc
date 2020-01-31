#include "bs_prim_mod_resets.h"

/* Constructor */
MOD_MakeReset::MOD_MakeReset(tSimStateHdl simHdl,
			     const char* name, Module* parent_mod,
			     unsigned int cycles, tUInt8 init, tUInt8 async)
    : Module(simHdl, name, parent_mod),
      sync(simHdl, "rstSync", this, cycles, async),
      rst_reset_value(init),
      written(~bk_now(sim_hdl))
{
  reset_fn = NULL;
  rst = 1;
  old_rst = rst;
  in_reset = false;
}

void MOD_MakeReset::static_reset_syncRst$rst(void *my_this, tUInt8 rst_in)
{
  ((MOD_MakeReset *)(my_this))->reset_syncRst$rst(rst_in);
}

void MOD_MakeReset::static_reset_syncRst$gen_rst(void *my_this, tUInt8 rst_in)
{
  ((MOD_MakeReset *)(my_this))->reset_syncRst$gen_rst(rst_in);
}


void MOD_ResetMux::static_do_select(void *my_this, tUInt8 /* rst_in */)
{
  ((MOD_ResetMux *)(my_this))->do_select();
}

