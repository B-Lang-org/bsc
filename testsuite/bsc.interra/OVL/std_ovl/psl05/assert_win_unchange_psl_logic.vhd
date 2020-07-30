-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--*********************************************************
-- Module to be replicated for assert checks
-- This module is bound to a PSL vunits with assert checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_win_unchange_assert is

        generic
        (width : integer        :=8);
        port
        (clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic; test_expr : std_logic_vector(width - 1 downto 0);  xzdetect_test_expr : std_logic; xzcheck_enable : ovl_ctrl);

end entity;

architecture rtl of assert_win_unchange_assert is
begin
end architecture;

--*********************************************************
-- Module to be replicated for assume checks
-- This module is bound to a PSL vunits with assume checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_win_unchange_assume is 
       generic
        (width : integer        :=8);
        port
        (clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic; test_expr : std_logic_vector(width - 1 downto 0);  xzdetect_test_expr : std_logic; xzcheck_enable : ovl_ctrl);

end entity;

architecture rtl of assert_win_unchange_assume is
begin
end architecture;

--*********************************************************
-- Module to be replicated for cover properties
-- This module is bound to a PSL vunit with cover properties
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_win_unchange_cover is
	generic
        (OVL_COVER_BASIC_ON : ovl_coverage_level	:= 1);

	port
	(clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic); 
end entity;

architecture rtl of assert_win_unchange_cover is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_win_unchange is
        constant assert_name            :string := "OVL_WIN_UNCHANGE";
        constant path                   :string := rtl'path_name;

        signal reset_n                  :std_logic;
        signal clk                      :std_logic;
        signal window                   :std_logic      := '0';
        signal xzdetect_test_expr	:std_logic	:= '0';

component assert_win_unchange_assert is
        generic
        (width : integer        :=8);
        port
        (clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic; test_expr : std_logic_vector(width - 1 downto 0); xzdetect_test_expr : std_logic; xzcheck_enable : ovl_ctrl);

end component;

component assert_win_unchange_assume is
        generic
        (width : integer        :=8);
        port
        (clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic; test_expr : std_logic_vector(width - 1 downto 0); xzdetect_test_expr : std_logic; xzcheck_enable : ovl_ctrl);

end component;

component assert_win_unchange_cover is
        generic
        (OVL_COVER_BASIC_ON : ovl_coverage_level        := 1);

        port
        (clk : std_logic; reset_n : std_logic; start_event : std_logic; end_event : std_logic;
         window : std_logic);

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
-- Assign signals                                                   --
------------------------------------------------------------------------------
p1: process (clk) is
begin
  if (clk'event and clk = '1') then
   if (reset_n /= '0') then
      if ( (window = '0') and (start_event = '1') ) then
        window <= '1';
      elsif ( (window = '1') and (end_event = '1') ) then
        window <= '0';
      end if;

    else
        window <= '0';
   end if;
  end if;
end process p1;

p2: process (test_expr) is
   variable x : std_logic;
   variable y : std_logic;
begin

   x := xor_reduce(test_expr);
   y := x xor x;

   if (y = '0') then
        xzdetect_test_expr <= '1';
   else
        xzdetect_test_expr <= '0';
   end if;

end process p2;

------------------------------------------------------------------------------
-- Assert Property                                                   --
------------------------------------------------------------------------------
ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_win_unchange : assert_win_unchange_assert
	generic map
	( width => width)      
	port map
        ( clk => clk, reset_n => reset_n, start_event => start_event, end_event => end_event, test_expr => test_expr, window => window, 
	  xzdetect_test_expr => xzdetect_test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assert_on_gen;

------------------------------------------------------------------------------
-- Assume Property                                                   --
------------------------------------------------------------------------------
ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_win_unchange : assert_win_unchange_assume
        generic map
        ( width => width)
        port map
        ( clk => clk, reset_n => reset_n, start_event => start_event, end_event => end_event, test_expr => test_expr, window => window,           
	 xzdetect_test_expr => xzdetect_test_expr, xzcheck_enable => controls.xcheck_ctrl);

 end generate ovl_assume_on_gen;

-----------------------------------------------------------------------------
-- Cover Property                                                   --
------------------------------------------------------------------------------
 ovl_cover_on_gen : if ( coverage_level /= OVL_COVER_NONE and controls.cover_ctrl = OVL_ON) generate
  cover_win_unchange : assert_win_unchange_cover
      generic map
        ( OVL_COVER_BASIC_ON => coverage_level)
      port map
        (clk => clk, reset_n => reset_n, start_event => start_event, end_event => end_event, window => window);
  end generate ovl_cover_on_gen;
end architecture;
