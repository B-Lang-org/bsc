-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

entity std_ovl_clock_gating is
  generic (
    clock_edge  : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    gating_type : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls    : ovl_ctrl_record    := OVL_CTRL_DEFAULTS  
  );
  port (
    clock       : in  std_logic;
    enable      : in  std_logic;
    clk         : out std_logic
  );
end entity std_ovl_clock_gating;

architecture rtl of std_ovl_clock_gating is
  constant clock_edge_ctrl  : ovl_active_edges_natural := 
    ovl_get_ctrl_val(clock_edge,  controls.clock_edge_default);
  constant gating_type_ctrl : ovl_gating_type_natural  := 
    ovl_get_ctrl_val(gating_type, controls.gating_type_default);
begin
  
  ovl_on_gen : if ((controls.assert_ctrl = OVL_ON) or (controls.cover_ctrl = OVL_ON)) generate
    ----------------------------------------------------------------------------
    -- Gated clock                                                            --
    ---------------------------------------------------------------------------- 
    ovl_gating_on_gen : if ((controls.gating_ctrl = OVL_ON) and (gating_type_ctrl = OVL_GATE_CLOCK)) generate
      -- non-inverted clock
      ovl_noninv_clk_gen : if (clock_edge_ctrl = OVL_POSEDGE) generate
        ovl_clock_gating_p : process (clock, enable)
          variable clken : std_logic;
        begin
          if (clock = '0') then
            clken := enable;
          end if;

          clk <= clock and clken;
        end process ovl_clock_gating_p;
      end generate ovl_noninv_clk_gen;
      
      -- inverted clock
      ovl_inv_clk_gen : if (clock_edge_ctrl /= OVL_POSEDGE) generate
        ovl_clock_gating_p : process (clock, enable)
          variable clken : std_logic;
        begin
          if (clock = '0') then
            clken := enable;
          end if;

          clk <= not (clock and clken);
        end process ovl_clock_gating_p;
      end generate ovl_inv_clk_gen;      
    end generate ovl_gating_on_gen;

    ----------------------------------------------------------------------------
    -- Non-gated clock                                                        --
    ---------------------------------------------------------------------------- 
    ovl_gating_off_gen : if ((controls.gating_ctrl = OVL_OFF) or (gating_type_ctrl /= OVL_GATE_CLOCK)) generate
      -- non-inverted clock
      ovl_noninv_clk_gen : if (clock_edge_ctrl = OVL_POSEDGE) generate
        clk <= clock;
      end generate ovl_noninv_clk_gen;
      
      -- inverted clock
      ovl_inv_clk_gen : if (clock_edge_ctrl /= OVL_POSEDGE) generate
        clk <= not clock;
      end generate ovl_inv_clk_gen;
    end generate ovl_gating_off_gen;
  end generate ovl_on_gen;
  
  ovl_off_gen : if ((controls.assert_ctrl = OVL_OFF) and (controls.cover_ctrl = OVL_OFF)) generate  
    clk <= '0';
  end generate ovl_off_gen;
  
end architecture rtl;
