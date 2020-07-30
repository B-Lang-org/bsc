-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_range is 
  constant assert_name         : string := "OVL_RANGE";
  constant path                : string := rtl'path_name;

  constant coverage_level_ctrl : ovl_coverage_level := ovl_get_ctrl_val(coverage_level, controls.coverage_level_default);
  constant cover_sanity        : boolean := cover_item_set(coverage_level_ctrl, OVL_COVER_SANITY); 
  constant cover_corner        : boolean := cover_item_set(coverage_level_ctrl, OVL_COVER_CORNER); 

  signal reset_n               : std_logic;
  signal clk                   : std_logic;
  signal fatal_sig             : std_logic;
  
  signal test_expr_x01         : std_logic_vector(width - 1 downto 0);
  signal prev_test_expr        : std_logic_vector(width - 1 downto 0);
  
  shared variable error_count  : natural;
  shared variable cover_count  : natural; 
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
        elsif (not ovl_is_x(test_expr_x01)) then
          if((unsigned(test_expr_x01) < min) or (unsigned(test_expr_x01) > max)) then
            fire(0) <= '1';
            ovl_error_proc("Test expression evaluates to a value outside the range specified by parameters min and max", severity_level,
                          property_type, assert_name, msg, path, controls, fatal_sig, error_count);
          else
            fire(0) <= '0';
          end if;
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
  ovl_cover_on_gen : if ((controls.cover_ctrl = OVL_ON) and (cover_sanity or cover_corner)) generate
    ovl_cover_p : process (clk)
    begin
      if (rising_edge(clk)) then
        prev_test_expr <= test_expr_x01;

        if (reset_n = '0') then 
          fire(2) <= '0';
        else
          fire(2) <= '0';
          
          if (cover_sanity and (test_expr_x01 /= prev_test_expr) and 
              not ovl_is_x(test_expr_x01) and not ovl_is_x(prev_test_expr)) then
            ovl_cover_proc("test_expr_change covered", assert_name, path, controls, cover_count);
            fire(2) <= '1';
          end if;
          
          if (cover_corner and (unsigned(test_expr_x01) = min) and not ovl_is_x(test_expr_x01)) then
            ovl_cover_proc("test_expr_at_min covered", assert_name, path, controls, cover_count);
            fire(2) <= '1';
          end if;
          
          if (cover_corner and (unsigned(test_expr_x01) = max) and not ovl_is_x(test_expr_x01)) then
            ovl_cover_proc("test_expr_at_max covered", assert_name, path, controls, cover_count);
            fire(2) <= '1';
          end if;          
        end if;
      end if;
    end process ovl_cover_p;    
  end generate ovl_cover_on_gen;
  
  ovl_cover_off_gen : if ((controls.cover_ctrl = OVL_OFF) or (not(cover_sanity) and not(cover_corner))) generate
    fire(2) <= '0';
  end generate ovl_cover_off_gen;
end architecture rtl;
