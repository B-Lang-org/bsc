-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--*********************************************************
-- Module to be replicated for assert checks
-- This module is bound to a PSL vunits with assert checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_width_assert is
	generic
	(min_cks : integer	:= 1; max_cks : integer	:= 2; checked_max_cks : integer := 1);
	port
	(clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_width_assert is
begin
end architecture;

--*********************************************************
-- Module to be replicated for assume checks
-- This module is bound to a PSL vunits with assume checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_width_assume is
        generic
        (min_cks : integer      := 1; max_cks : integer := 2; checked_max_cks : integer := 1);
        port
        (clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_width_assume is
begin
end architecture;

--*********************************************************
-- Module to be replicated for cover properties
-- This module is bound to a PSL vunit with cover properties
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_width_cover is
        generic
        (min_cks : integer      := 1; max_cks : integer := 2; OVL_COVER_BASIC_ON : ovl_coverage_level	:= 1; OVL_COVER_CORNER_ON : ovl_coverage_level := 1;
	 checked_min_cks : integer := 0; checked_max_cks : integer := 1);
	port
        (clk : std_logic; reset_n : std_logic; test_expr : std_logic);
end entity;

architecture rtl of assert_width_cover is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_width is
        constant assert_name    :string := "OVL_WIDTH";
        constant path           :string := rtl'path_name;

        signal reset_n          :std_logic;
        signal clk              :std_logic;

component assert_width_assert is
        generic
        (min_cks : integer      := 1; max_cks : integer := 2; checked_max_cks : integer := 1);
        port
        (clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end component;

component assert_width_assume is
        generic
        (min_cks : integer      := 1; max_cks : integer := 2; checked_max_cks : integer := 1);
        port
        (clk : std_logic; reset_n : std_logic; test_expr : std_logic; xzcheck_enable : ovl_ctrl);
end component;

component assert_width_cover is
        generic
        (min_cks : integer      := 1; max_cks : integer := 2; OVL_COVER_BASIC_ON : ovl_coverage_level := 1; OVL_COVER_CORNER_ON : ovl_coverage_level := 1;
	 checked_min_cks : integer := 0; checked_max_cks : integer := 1);
        port
        (clk : std_logic; reset_n : std_logic; test_expr : std_logic);
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
-- Check if min_cks less than max_cks or not
------------------------------------------------------------------------------
p1: process(clk)
begin
 if(clk='1' and clk'event) then
    if ((max_cks > 0) and (min_cks > max_cks)) then
       report("Info:*** Illegal parameter values set where min_cks > max_cks");
    end if;
 end if;
end process p1;

------------------------------------------------------------------------------
-- Assert Property                                                   --
------------------------------------------------------------------------------

 ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_width: assert_width_assert
      generic map
        ( min_cks => min_cks, max_cks => max_cks, checked_max_cks => check_condition_integer(max_cks>0, max_cks-1, 0))
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assert_on_gen;

------------------------------------------------------------------------------
-- Assume Property                                                   --
------------------------------------------------------------------------------

 ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assume_width: assert_width_assume
      generic map
        ( min_cks => min_cks, max_cks => max_cks, checked_max_cks => check_condition_integer(max_cks>0, max_cks-1, 1))
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assume_on_gen;

------------------------------------------------------------------------------
-- Cover Property                                                   --
------------------------------------------------------------------------------
 ovl_cover_on_gen : if ( coverage_level /= OVL_COVER_NONE and controls.cover_ctrl = OVL_ON) generate
  cover_width : assert_width_cover
      generic map
        ( min_cks => min_cks, max_cks => max_cks, OVL_COVER_BASIC_ON => coverage_level, OVL_COVER_CORNER_ON => coverage_level,
	checked_min_cks => check_condition_integer(min_cks>0, min_cks-1, 1),checked_max_cks => check_condition_integer(max_cks>0, max_cks-1, 1))
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr);
  end generate ovl_cover_on_gen;

end architecture;
