-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--************************************************************
-- Module to be replicated for assert checks
-- This module is bound to the PSL vunits with assert checks
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_one_cold_assert is

        generic
        (width : integer        := 8; inactive :ovl_inactive    := OVL_ONE_COLD);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl; inactive_val : std_logic;
         test_expr : std_logic_vector(width-1 downto 0));

end entity;

architecture rtl of assert_one_cold_assert is
begin
end architecture;

--************************************************************
-- Module to be replicated for assume checks
-- This module is bound to the PSL vunits with assume checks
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_one_cold_assume is
        
        generic
        (width : integer        := 8; inactive : ovl_inactive    := OVL_ONE_COLD);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl; inactive_val : std_logic;          
         test_expr : std_logic_vector(width-1 downto 0));

end entity;

architecture rtl of assert_one_cold_assume is
begin
end architecture;

--************************************************************
-- Module to be replicated for cover properties
-- This module is bound to the PSL vunits with cover properties
--***********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_one_cold_cover is

        generic
        (width : integer        := 8; inactive : ovl_inactive    := 2;
         OVL_COVER_SANITY_ON : ovl_coverage_level := 1; OVL_COVER_CORNER_ON : ovl_coverage_level := 1);

        port
        (clk : std_logic; reset_n : std_logic; inactive_val : std_logic;
         test_expr : std_logic_vector(width-1 downto 0); one_colds_checked : std_logic_vector(width-1 downto 0));

end entity;

architecture rtl of assert_one_cold_cover is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_one_cold is
        constant assert_name    :string := "OVL_ONE_COLD";
        constant path           :string := rtl'path_name;

        signal reset_n          :std_logic;
        signal clk              :std_logic;
        signal inactive_val     :std_logic;

        signal one_colds_checked : std_logic_vector(width-1 downto 0);
        
component assert_one_cold_assert is

        generic
        (width : integer        := 8; inactive :ovl_inactive    := 2);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl; inactive_val : std_logic;
         test_expr : std_logic_vector(width-1 downto 0));

end component;

component assert_one_cold_assume is

        generic
        (width : integer        := 8; inactive : ovl_inactive    := 2);

        port
        (clk : std_logic; reset_n : std_logic; xzcheck_enable : ovl_ctrl; inactive_val : std_logic;
         test_expr : std_logic_vector(width-1 downto 0));

end component;

component assert_one_cold_cover is

        generic
        (width : integer        := 8; inactive : ovl_inactive    := 2;
         OVL_COVER_SANITY_ON : ovl_coverage_level := 1; OVL_COVER_CORNER_ON : ovl_coverage_level := 1);

        port
        (clk : std_logic; reset_n : std_logic; inactive_val : std_logic;
         test_expr : std_logic_vector(width-1 downto 0); one_colds_checked : std_logic_vector(width-1 downto 0));

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
-- assign inactive_val                                                     --
------------------------------------------------------------------------------
p1: process(inactive_val)
begin
 if ( inactive = 1 ) then
        inactive_val <= '1';
 else
        inactive_val <= '0';
 end if;
end process p1;
------------------------------------------------------------------------------
-- Assert Property                                                   --
------------------------------------------------------------------------------
 ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

 assert_one_cold : assert_one_cold_assert
      generic map
        ( width => width, inactive => inactive )
      port map      
        (clk => clk, reset_n => reset_n, inactive_val => inactive_val, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assert_on_gen;

-------------------------------------------------------------------------------
-- Assume Property                                                          --
------------------------------------------------------------------------------
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_one_cold : assert_one_cold_assume
      generic map
        ( width => width, inactive => inactive )
      port map
        (clk => clk, reset_n => reset_n, inactive_val => inactive_val, test_expr => test_expr, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assume_on_gen; 

------------------------------------------------------------------------------
-- assign one_colds_checked                                                   --
------------------------------------------------------------------------------
p2: process(clk)  
 variable test_expr_i         : std_logic_vector(width-1 downto 0);
 variable test_expr_i_1         : std_logic_vector(width-1 downto 0);

begin
  if ( clk'event and clk = '1' and controls.cover_ctrl = OVL_ON) then
   if (reset_n /= '1') then
        one_colds_checked <= (width-1 downto 0 => '1');
        test_expr_i := (width-1 downto 0 => '1');
        test_expr_i_1 := (width-1 downto 0 => '1');
   else                         --check for known driven and zero one cold test_expr and update one_colds_checked
        test_expr_i := not(test_expr);
        if (test_expr_i > (width-1 downto 0 => '0')) then
                test_expr_i_1 := std_logic_vector(signed(test_expr_i) - 1 );
        else 
                test_expr_i_1 := (width-1 downto 0 => '0');
        end if;

        if ( (test_expr xor test_expr) = (width-1 downto 0 => '0') )
        and  ( (inactive > OVL_ALL_ONES) or (test_expr /= (width-1 downto 0 => inactive_val)) )
        and  ( not((test_expr_i = (width-1 downto 0 => '0')) or ((test_expr_i and test_expr_i_1) /= (width-1 downto 0 => '0'))) ) then
                one_colds_checked <= (one_colds_checked and test_expr);
        end if;

   end if;
  end if;
end process p2;

------------------------------------------------------------------------------
-- Coverage Property                                                   --
------------------------------------------------------------------------------

 ovl_cover_on_gen : if ( coverage_level /= OVL_COVER_NONE and controls.cover_ctrl = OVL_ON ) generate 
  cover_one_cold : assert_one_cold_cover
      generic map
        ( width => width, inactive => inactive, OVL_COVER_SANITY_ON => coverage_level, OVL_COVER_CORNER_ON => coverage_level)
      port map
        (clk => clk, reset_n => reset_n, test_expr => test_expr, one_colds_checked => one_colds_checked, inactive_val => inactive_val);
 end generate ovl_cover_on_gen;

end architecture;
