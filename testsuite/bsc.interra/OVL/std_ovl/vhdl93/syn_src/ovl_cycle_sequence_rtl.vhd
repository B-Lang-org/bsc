-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_cycle_sequence is 
  constant assert_name          : string := "OVL_CYCLE_SEQUENCE";
  constant path                 : string := "";
  
  constant trig_on_most_pipe    : boolean := (necessary_condition = OVL_TRIGGER_ON_MOST_PIPE); 
  constant trig_on_first_pipe   : boolean := (necessary_condition = OVL_TRIGGER_ON_FIRST_PIPE); 
  constant trig_on_first_nopipe : boolean := (necessary_condition = OVL_TRIGGER_ON_FIRST_NOPIPE); 

  constant coverage_level_ctrl  : ovl_coverage_level := ovl_get_ctrl_val(coverage_level,  controls.coverage_level_default);
  constant cover_basic          : boolean := cover_item_set(coverage_level_ctrl, OVL_COVER_BASIC); 

  signal reset_n                : std_logic;
  signal clk                    : std_logic;
  signal fatal_sig              : std_logic;
  
  signal event_sequence_x01     : std_logic_vector(num_cks - 1 downto 0);
  signal seq_queue              : std_logic_vector(num_cks - 1 downto 0);

  shared variable error_count   : natural;
  shared variable cover_count   : natural;
begin
  event_sequence_x01 <= to_x01(event_sequence);
  
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
  -- Shared logic                                                             --
  ------------------------------------------------------------------------------ 
  ovl_seq_queue_gen : if (ovl_2state_is_on(controls, property_type) or
                          ((controls.cover_ctrl = OVL_ON) and (coverage_level_ctrl /= OVL_COVER_NONE))) generate
    ovl_seq_queue_p : process (clk)
    begin
      if (rising_edge(clk)) then
        if (reset_n = '0') then
          seq_queue <= (others => '0');
        else
          if (trig_on_first_nopipe) then
            seq_queue(num_cks - 1) <= not(or_reduce(seq_queue(num_cks - 1 downto 1))) and 
                                      event_sequence_x01(num_cks - 1);
          else
            seq_queue(num_cks - 1) <= event_sequence_x01(num_cks - 1);
          end if;
          
          seq_queue(num_cks - 2 downto 0) <= seq_queue(num_cks - 1 downto 1) and 
                                             event_sequence_x01(num_cks - 2 downto 0);
        end if;
      end if;
    end process ovl_seq_queue_p;
  end generate ovl_seq_queue_gen;

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
        else
        
          fire(0) <= '0';
          if (trig_on_first_pipe or trig_on_first_nopipe) then
            if (and_reduce((seq_queue(num_cks -1 downto 1) and event_sequence_x01(num_cks - 2 downto 0)) or
                        not(seq_queue(num_cks -1 downto 1))) = '0') then
            fire(0) <= '1';
            ovl_error_proc("First event occured but it is not followed by the rest of the events in sequence", 
                           severity_level, property_type, assert_name, msg, path, controls, fatal_sig, error_count);
            end if;
          else -- trig_on_most_pipe
            if ((not(seq_queue(1)) or (seq_queue(1) and event_sequence_x01(0))) = '0') then
              fire(0) <= '1';
              ovl_error_proc("First num_cks-1 events occured but they are not followed by the last event in sequence", 
                             severity_level, property_type, assert_name, msg, path, controls, fatal_sig, error_count);            
            end if;
          end if;
          
        end if; -- reset_n = '0'
      end if; -- rising_edge(clk)
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
      function init_valid_sequence_gate return std_logic_vector is
        variable set : std_logic_vector(num_cks - 2 downto 0);
      begin
        if (num_cks > 2) then
          set(num_cks - 2 downto 1) := (others => '1');
        end if;
        if (trig_on_most_pipe) then set(0) := '0'; else set(0) := '1'; end if;
        return set;
      end function init_valid_sequence_gate;

      variable valid_first_event      : std_logic;
      variable valid_sequence         : std_logic;
      variable valid_last_event       : std_logic;
      constant valid_sequence_gate    : std_logic_vector(num_cks - 2 downto 0) := init_valid_sequence_gate;
    begin
      if (rising_edge(clk)) then
        fatal_sig <= 'Z';
        valid_first_event := event_sequence_x01(num_cks - 1);
        valid_last_event  := seq_queue(1) and event_sequence_x01(0);
        valid_sequence    := xor_reduce(seq_queue(num_cks - 1 downto 1) and event_sequence_x01(num_cks - 2 downto 0) and 
                                        valid_sequence_gate);
        if (reset_n = '0') then
          fire(1) <= '0';
        else
          fire(1) <= '0';
          
          if (ovl_is_x(valid_first_event)) then
            if (trig_on_most_pipe or trig_on_first_pipe) then
              fire(1) <= '1';
              ovl_error_proc("First event in the sequence contains X, Z, U, W or -", severity_level, property_type, 
                             assert_name, msg, path, controls, fatal_sig, error_count);
            elsif (not(or_reduce(seq_queue(num_cks - 1 downto 1))) = '1') then
              fire(1) <= '1';
              ovl_error_proc("First event in the sequence contains X, Z, U, W or -", severity_level, property_type, 
                             assert_name, msg, path, controls, fatal_sig, error_count);
            end if;
          end if;
          
          if (ovl_is_x(valid_sequence)) then
            if (trig_on_first_pipe or trig_on_first_nopipe) then
              fire(1) <= '1';
              ovl_error_proc("Subsequent events in the sequence contain X, Z, U, W or -", severity_level, property_type, 
                             assert_name, msg, path, controls, fatal_sig, error_count);
            else
              fire(1) <= '1';
              ovl_error_proc("First num_cks-1 events in the sequence contain X, Z, U, W or -", severity_level, property_type, 
                             assert_name, msg, path, controls, fatal_sig, error_count);
            end if;
          end if;
          
          if (trig_on_most_pipe) then
            if (ovl_is_x(valid_last_event)) then
              if (seq_queue(1) = '1') then
                fire(1) <= '1';
                ovl_error_proc("Last event in the sequence contain X, Z, U, W or -", severity_level, property_type, 
                               assert_name, msg, path, controls, fatal_sig, error_count);
              else
                fire(1) <= '1';
                ovl_error_proc("First num_cks-1 events in the sequence contain X, Z, U, W or -", severity_level, property_type, 
                               assert_name, msg, path, controls, fatal_sig, error_count);
              end if;
            end if;
          end if;
          
        end if; -- reset_n = '0'
      end if; -- rising_edge(clk)
    end process ovl_xcheck_p;
  end generate ovl_xcheck_on_gen;
  
  ovl_xcheck_off_gen : if (not ovl_xcheck_is_on(controls, property_type, OVL_IMPLICIT_XCHECK)) generate
    fire(1) <= '0';
  end generate ovl_xcheck_off_gen;
  
  ------------------------------------------------------------------------------
  -- Coverage                                                                 --
  ------------------------------------------------------------------------------
  ovl_cover_on_gen : if ((controls.cover_ctrl = OVL_ON) and cover_basic) generate      
    ovl_cover_p : process (clk)
    begin
      if (rising_edge(clk)) then
        if (reset_n = '0') then
          fire(2) <= '0';
        elsif (((trig_on_first_pipe or trig_on_first_nopipe) and (event_sequence_x01(num_cks - 1) = '1')) or
               (trig_on_most_pipe and (seq_queue(1) = '1'))) then
          fire(2) <= '1';
          ovl_cover_proc("sequence_trigger covered", assert_name, path, controls, cover_count);
        else
          fire(2) <= '0';
        end if;
      end if;
    end process ovl_cover_p;
  end generate ovl_cover_on_gen;
  
  ovl_cover_off_gen : if ((controls.cover_ctrl = OVL_OFF) or not cover_basic) generate
    fire(2) <= '0';
  end generate ovl_cover_off_gen;
end architecture rtl;
