-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_always_assert is 
               port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_always_assert is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
entity assert_always_assume is 
               port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_always_assume is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_always is 
  constant assert_name         : string := "OVL_ALWAYS";
  constant path                : string := rtl'path_name;
  
  signal reset_n               : std_logic;
  signal clk                   : std_logic;

  component assert_always_assert is 
               port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
  end component;

  component assert_always_assume is 
               port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
  end component;

begin
  
  ------------------------------------------------------------------------------
  -- Gating logic                                                             --
  ------------------------------------------------------------------------------
  reset_gating : entity work.std_ovl_reset_gating
    generic map 
      (reset_polarity => reset_polarity, gating_type => gating_type, controls => controls)
    port map 
      (reset => reset, enable => enable, reset_n => reset_n);
  
  clock_gating : entity work.std_ovl_clock_gating
    generic map 
      (clock_edge => clock_edge, gating_type => gating_type, controls => controls)
    port map 
      (clock => clock, enable => enable, clk => clk);

  ------------------------------------------------------------------------------
  -- Initialization message                                                   --
  ------------------------------------------------------------------------------ 
  ovl_init_msg_gen : if (controls.init_msg_ctrl = OVL_ON) generate
    ovl_init_msg_proc(severity_level, property_type, assert_name, msg, path, controls);
  end generate ovl_init_msg_gen;

  ------------------------------------------------------------------------------
  -- Assert Property
  ------------------------------------------------------------------------------ 
  ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_always : assert_always_assert
      port map 
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
  
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_always : assert_always_assume
      port map 
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;
    
end architecture rtl;

