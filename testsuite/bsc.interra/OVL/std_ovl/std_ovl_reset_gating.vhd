-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

entity std_ovl_reset_gating is
  generic (
    reset_polarity : ovl_reset_polarity := OVL_ACTIVE_EDGES_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    reset          : in  std_logic;
    enable         : in  std_logic;
    reset_n        : out std_logic
  );
end entity std_ovl_reset_gating;

architecture rtl of std_ovl_reset_gating is
  signal greset                : std_logic;
        
  constant gating_on           : boolean                    := controls.gating_ctrl = OVL_ON;
  constant reset_polarity_ctrl : ovl_reset_polarity_natural := 
    ovl_get_ctrl_val(reset_polarity, controls.reset_polarity_default);
  constant gating_type_ctrl    : ovl_gating_type_natural    := 
    ovl_get_ctrl_val(gating_type, controls.gating_type_default);
begin
  
  ovl_on_gen : if ((controls.assert_ctrl = OVL_ON) or (controls.cover_ctrl = OVL_ON)) generate
    ----------------------------------------------------------------------------
    -- Global reset                                                           --
    ---------------------------------------------------------------------------- 
    ovl_global_reset_on_gen : if (controls.global_reset_ctrl = OVL_ON) generate
      reset_n <= ovl_global_reset_signal;
    end generate ovl_global_reset_on_gen;
    
    ovl_global_reset_off_gen : if (controls.global_reset_ctrl = OVL_OFF) generate
      --------------------------------------------------------------------------
      -- Gated reset                                                          --
      -------------------------------------------------------------------------- 
      ovl_gate_reset_gen : if (gating_on and (gating_type_ctrl = OVL_GATE_RESET)) generate
        greset <= reset and enable;        
      end generate ovl_gate_reset_gen;

      --------------------------------------------------------------------------
      -- Non-gated reset                                                      --
      -------------------------------------------------------------------------- 
      ovl_no_gate_reset_gen : if (gating_on and (gating_type_ctrl /= OVL_GATE_RESET)) generate
        greset <= reset;
      end generate ovl_no_gate_reset_gen;

      --------------------------------------------------------------------------
      -- Gating off                                                           --
      -------------------------------------------------------------------------- 
      ovl_gating_off_gen : if (not gating_on) generate
        greset <= reset;
      end generate ovl_gating_off_gen;

      ------------------------------------------------------------------------
      -- Inverted reset                                                     --
      ------------------------------------------------------------------------     
      ovl_reset_active_high_gen : if (reset_polarity_ctrl = OVL_ACTIVE_HIGH) generate
        reset_n <= not greset;
      end generate ovl_reset_active_high_gen;                 
      
      ------------------------------------------------------------------------
      -- Non-inverted reset                                                     --
      ------------------------------------------------------------------------     
      ovl_reset_active_low_gen : if (reset_polarity_ctrl = OVL_ACTIVE_LOW) generate
        reset_n <= greset;
      end generate ovl_reset_active_low_gen;                 
    end generate ovl_global_reset_off_gen;
  end generate ovl_on_gen;
  
  ovl_off_gen : if ((controls.assert_ctrl = OVL_OFF) and (controls.cover_ctrl = OVL_OFF)) generate  
    reset_n <= '0';
  end generate ovl_off_gen;

end architecture rtl;
