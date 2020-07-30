-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--*********************************************************
-- Module to be replicated for assert checks
-- This module is bound to the PSL vunits with assert checks
--*********************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_proposition_assert is 
	port
	( reset_n : std_logic; test_expr : std_logic; xzdetect_bit : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_proposition_assert is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_proposition is
        constant assert_name    :string := "OVL_PROPOSITION";
        constant path           :string := rtl'path_name;

        signal reset_n          :std_logic;
	
	signal psl_valid_test_expr : std_logic;
	signal xzdetect_bit : std_logic;

 component assert_proposition_assert is
        port
        (reset_n : std_logic; test_expr : std_logic; xzdetect_bit : std_logic; xzcheck_enable : ovl_ctrl);

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

------------------------------------------------------------------------------
-- Initialization message                                                   --
------------------------------------------------------------------------------
  ovl_init_msg_gen : if (controls.init_msg_ctrl = OVL_ON) generate
    ovl_init_msg_proc(severity_level, property_type, assert_name, msg, path, controls);
  end generate ovl_init_msg_gen;

------------------------------------------------------------------------------
-- assign psl_valid_test_expr                                                   --
------------------------------------------------------------------------------
psl_valid_test_expr <= not(test_expr xor test_expr);

p1: process (reset_n, psl_valid_test_expr)
 begin
  if (reset_n = '0') then
	xzdetect_bit <= '0';
  else
    if ( psl_valid_test_expr = '1') then
  	-- Do nothing
    else
	xzdetect_bit <= not(xzdetect_bit);
    end if;
  end if;
end process p1;	
------------------------------------------------------------------------------
-- Assert Property                                                   	    --
------------------------------------------------------------------------------

 ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate

  assert_proposition : assert_proposition_assert
      port map
        ( reset_n => reset_n, test_expr => test_expr, xzdetect_bit => xzdetect_bit, xzcheck_enable => controls.xcheck_ctrl);
 end generate ovl_assert_on_gen;



-- Note: This is an unclocked/immediate assertion based checker
--      Immediate assertions can't be assumptions.
--      Assume is only available in a concurrent (clocked) form of an 
--      assertion statement. Hence, this checker does not implement
--      assumption of the properties.
end architecture;

