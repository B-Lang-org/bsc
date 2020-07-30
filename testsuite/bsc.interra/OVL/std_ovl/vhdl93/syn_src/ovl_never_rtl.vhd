-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_never is 
  constant assert_name        : string := "OVL_NEVER";
  constant path               : string := "";

  signal reset_n              : std_logic;
  signal clk                  : std_logic;
  signal fatal_sig            : std_logic;

  signal test_expr_x01         : std_logic;

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
  -- Assertion - 2-STATE                                                      --
  ------------------------------------------------------------------------------
  ovl_assert_on_gen : if (ovl_2state_is_on(controls, property_type)) generate      
    ovl_assert_p : process (clk)
    begin
      if (rising_edge(clk)) then
        fatal_sig <= 'Z';
        if (reset_n = '0') then
          fire(0) <= '0';
        elsif (to_x01(test_expr_x01) = '1') then
          fire(0) <= '1';
          ovl_error_proc("Test expression is not FALSE", severity_level, property_type, 
                         assert_name, msg, path, controls, fatal_sig, error_count);
        else
          fire(0) <= '0';
        end if;
      end if;
    end process ovl_assert_p;
    
    ovl_finish_proc(assert_name, path, controls.runtime_after_fatal, fatal_sig);
  end generate ovl_assert_on_gen;
  
  ovl_assert_off_gen : if (not ovl_2state_is_on(controls, property_type)) generate      
    fire(0) <= '0';
  end generate ovl_assert_off_gen;
  
  ------------------------------------------------------------------------------
  -- Assertion - X-CHECK                                                      --
  ------------------------------------------------------------------------------
  ovl_xcheck_on_gen : if (ovl_xcheck_is_on(controls, property_type, OVL_IMPLICIT_XCHECK)) generate
    ovl_xcheck_p : process (clk)
    begin
      if (rising_edge(clk)) then
        fatal_sig <= 'Z';
        if (reset_n = '0') then
          fire(1) <= '0';
        elsif (ovl_is_x(test_expr_x01)) then
          fire(1) <= '1';
          ovl_error_proc("test_expr contains X, Z, U, W or -", severity_level, property_type, 
                         assert_name, msg, path, controls, fatal_sig, error_count);
        else
          fire(1) <= '0';
        end if;
      end if;
    end process ovl_xcheck_p;
  end generate ovl_xcheck_on_gen;
  
  ovl_xcheck_off_gen : if (not ovl_xcheck_is_on(controls, property_type, OVL_IMPLICIT_XCHECK)) generate
    fire(1) <= '0';
  end generate ovl_xcheck_off_gen;

  ------------------------------------------------------------------------------
  -- Coverage                                                                 --
  ------------------------------------------------------------------------------ 
  -- No coverage for this checker.
  fire(2) <= '0';
    
end architecture rtl;
