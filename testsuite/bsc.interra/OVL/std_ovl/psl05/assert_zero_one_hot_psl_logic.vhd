-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--***********************************************************
-- Module to be replicated for assert checks
-- This module is bound to the PSL vunits with assert checks
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_zero_one_hot_assert is
        generic
        (width : integer                := 1);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl;
        test_expr : std_logic_vector(width-1 downto 0));

end entity;

architecture rtl of assert_zero_one_hot_assert is
begin
end architecture;


--***********************************************************
-- Module to be replicated for assume checks
-- This module is bound to a PSL vunits with assume checks
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_zero_one_hot_assume is 
        generic
        (width : integer                := 1);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl;
        test_expr : std_logic_vector(width-1 downto 0));

end entity;

architecture rtl of assert_zero_one_hot_assume is
begin
end architecture;


--***********************************************************
-- Module to be replicated for cover properties
-- This module is bound to a PSL vunit with cover properties
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
entity assert_zero_one_hot_cover is
	
	generic
        (width : integer                := 1;
        OVL_COVER_SANITY_ON : ovl_coverage_level                := 1; OVL_COVER_CORNER_ON : ovl_coverage_level                := 1);

	port
        (clk : std_logic; reset_n : std_logic;
        test_expr : std_logic_vector(width-1 downto 0); all_one_hots_checked : std_logic);

end entity;

architecture rtl of assert_zero_one_hot_cover is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_zero_one_hot is
        constant assert_name    :string := "OVL_ZERO_ONE_HOT";
        constant path           :string := rtl'path_name;

        signal reset_n          :std_logic;
        signal clk              :std_logic;

        signal all_one_hots_checked 	: std_logic	:= '0';
        signal one_hots_checked 	: std_logic_vector(width-1 downto 0);

component assert_zero_one_hot_assert is
        generic
        (width : integer                := 1);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl;
        test_expr : std_logic_vector(width-1 downto 0));

end component;

component assert_zero_one_hot_assume is
        generic
        (width : integer                := 1);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl;
        test_expr : std_logic_vector(width-1 downto 0));

end component;

component assert_zero_one_hot_cover is

        generic
        (width : integer                := 1;
        OVL_COVER_SANITY_ON : ovl_coverage_level                := 1; OVL_COVER_CORNER_ON : ovl_coverage_level                := 1);

        port
        (clk : std_logic; reset_n : std_logic;
        test_expr : std_logic_vector(width-1 downto 0); all_one_hots_checked : std_logic);

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
 ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

 assert_zero_one_hot : assert_zero_one_hot_assert
      generic map
        ( width => width )
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assert_on_gen;

-------------------------------------------------------------------------------
-- Assume Property                                                          --
------------------------------------------------------------------------------
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_zero_one_hot : assert_zero_one_hot_assume
      generic map
        ( width => width )
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assume_on_gen;

------------------------------------------------------------------------------
-- assign one_hots_checked                                                   --
------------------------------------------------------------------------------
p1: process(clk)
	
   variable test_expr_1		: std_logic_vector(width-1 downto 0);
begin
  if ( clk'event and clk = '1' and controls.cover_ctrl = OVL_ON) then
   if (reset_n /= '1') then
    	test_expr_1 := (width-1 downto 0 => '0');
    	one_hots_checked <= (width-1 downto 0 => '0');

   else                         --check for known driven and zero one hot test_expr and update one_hots_checked
	  test_expr_1 := std_logic_vector(unsigned(test_expr) - 1);
	  if ( ((test_expr xor test_expr) = (width-1 downto 0 => '0')) and ((test_expr and test_expr_1) = (width-1 downto 0 => '0')) ) then
		  one_hots_checked <= (one_hots_checked or test_expr); 
   	end if;

     end if;
  end if;
end process p1;


p2: process (one_hots_checked) 
begin
	if (one_hots_checked = (width-1 downto 0 => '1')) then
		all_one_hots_checked <= '1';
	else
		all_one_hots_checked <= '0';
	end if;
	
end process p2;

------------------------------------------------------------------------------
-- Coverage Property                                                   --
------------------------------------------------------------------------------

 ovl_cover_on_gen : if ( coverage_level /= OVL_COVER_NONE and controls.cover_ctrl = OVL_ON ) generate
  cover_zero_one_hot : assert_zero_one_hot_cover
      generic map
        ( width => width, OVL_COVER_SANITY_ON => coverage_level, OVL_COVER_CORNER_ON => coverage_level)
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, all_one_hots_checked => all_one_hots_checked);
 end generate ovl_cover_on_gen;

end architecture;
