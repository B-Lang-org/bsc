-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

-- $$ Special comments:
-- $$  'reset_n' added to checker process sensitivity list to enable immediate check upon reset deactivation 

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_never_unknown_async is 
  constant assert_name        : string := "OVL_NEVER_UNKNOWN_ASYNC";
  constant path               : string := "";

  signal reset_n              : std_logic;
  signal fatal_sig            : std_logic;
  
  signal test_expr_x01        : std_logic_vector(width - 1 downto 0);

  shared variable error_count : natural;
begin
  test_expr_x01 <= to_x01(test_expr);
  
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
  -- Assertion - 2-STATE                                                      --
  ------------------------------------------------------------------------------
  -- No 2-state assertion for this checker. 
  fire(0) <= '0';
 
  ------------------------------------------------------------------------------
  -- Assertion - X-CHECK                                                      --
  ------------------------------------------------------------------------------
  ovl_xcheck_on_gen : if (ovl_xcheck_is_on(controls, property_type, OVL_EXPLICIT_XCHECK)) generate      
    ovl_assert_p : process (reset_n, test_expr_x01)
    begin
      fatal_sig <= 'Z';
      if (reset_n = '0') then
        fire(1) <= '0';
      elsif ((reset_n = '1') and ovl_is_x(test_expr_x01)) then
        fire(1) <= '1';
        ovl_error_proc("test_expr contains X, Z, U, W or -", severity_level, property_type, 
                       assert_name, msg, path, controls, fatal_sig, error_count);
      else
        fire(1) <= '0';
      end if;
    end process ovl_assert_p;
    
    ovl_finish_proc(assert_name, path, controls.runtime_after_fatal, fatal_sig);
  end generate ovl_xcheck_on_gen;
  
  ovl_xcheck_off_gen : if (not ovl_xcheck_is_on(controls, property_type, OVL_EXPLICIT_XCHECK)) generate
    fire(1) <= '0';
  end generate ovl_xcheck_off_gen;

  ------------------------------------------------------------------------------
  -- Coverage                                                                 --
  ------------------------------------------------------------------------------ 
  -- No coverage for this checker.
  fire(2) <= '0';
  
end architecture rtl;
