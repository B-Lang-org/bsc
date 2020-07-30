-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--*********************************************************
-- Module to be replicated for assert checks
-- This module is bound to a PSL vunits with assert checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_quiescent_state_assert is
	generic
        (width : integer         :=8);

        port
        (clk : std_logic; reset_n : std_logic; sample_event : std_logic; state_expr : std_logic_vector(width-1 downto 0);
        check_value : std_logic_vector(width - 1 downto 0); end_of_simulation : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_quiescent_state_assert is
begin
end architecture;

--*********************************************************
-- Module to be replicated for assume checks
-- This module is bound to a PSL vunits with assume checks
--*********************************************************
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_quiescent_state_assume is
        generic
        (width : integer         :=8);

        port
        (clk : std_logic; reset_n : std_logic; sample_event : std_logic; state_expr : std_logic_vector(width-1 downto 0);
        check_value : std_logic_vector(width - 1 downto 0); end_of_simulation : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_quiescent_state_assume is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_quiescent_state is
        constant assert_name    :string := "OVL_QUIESCENT_STATE";
        constant path           :string := rtl'path_name;

        signal reset_n          :std_logic;
        signal clk              :std_logic;

	signal end_of_simulation	: std_logic;

component assert_quiescent_state_assert is
        generic
        (width : integer         :=8);

        port
        (clk : std_logic; reset_n : std_logic; sample_event : std_logic; state_expr : std_logic_vector(width-1 downto 0);
        check_value : std_logic_vector(width - 1 downto 0); end_of_simulation : std_logic; xzcheck_enable : ovl_ctrl);

end component;

component assert_quiescent_state_assume is
        generic
        (width : integer         :=8);

        port
        (clk : std_logic; reset_n : std_logic; sample_event : std_logic; state_expr : std_logic_vector(width-1 downto 0);
        check_value : std_logic_vector(width - 1 downto 0); end_of_simulation : std_logic; xzcheck_enable : ovl_ctrl);

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
-- Assert Property                                                   --
------------------------------------------------------------------------------

end_of_simulation <= ovl_end_of_simulation_signal;

 ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_quiescent_state : assert_quiescent_state_assert
      generic map
        ( width => width )
      port map
        (clk => clk, reset_n => reset_n, state_expr => state_expr, check_value => check_value, sample_event => sample_event, 
	end_of_simulation => end_of_simulation, xzcheck_enable => controls.xcheck_ctrl);

 end generate ovl_assert_on_gen;

------------------------------------------------------------------------------
-- Assume Property                                                   --
------------------------------------------------------------------------------

end_of_simulation <= ovl_end_of_simulation_signal;

 ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assume_quiescent_state : assert_quiescent_state_assume
      generic map
        ( width => width )
      port map
        (clk => clk, reset_n => reset_n, state_expr => state_expr, check_value => check_value, sample_event => sample_event,
        end_of_simulation => end_of_simulation, xzcheck_enable => controls.xcheck_ctrl);

 end generate ovl_assume_on_gen;
end architecture;
