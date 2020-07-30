-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_frame_assert is 
  generic (
    min_cks          : integer   := 1; 
    max_cks          : integer   := 2;
    min_cks_resolved : integer   := 1;
   -- To replace check_condition_integer(min_cks>1, min_cks-1, 1) as function call not supported in repetition in some simulators
    max_cks_resolved : integer   := 1
  );
  port(clk : std_logic; reset_n : std_logic; start_event : std_logic ; test_expr : std_logic; win : std_logic ; ignore_new_start : std_logic ; reset_on_new_start : std_logic; error_on_new_start : std_logic ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_frame_assert is
begin
end architecture;


--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_frame_assume is 
  generic (
    min_cks          : integer   := 1; 
    max_cks          : integer   := 2;
    min_cks_resolved : integer   := 1;
    max_cks_resolved : integer   := 1
   -- To replace check_condition_integer(min_cks>1, min_cks-1, 1) as function call not supported in repetition in some simulators
  );
  port(clk : std_logic; reset_n : std_logic; start_event : std_logic ; test_expr : std_logic;  win : std_logic ; ignore_new_start : std_logic ; reset_on_new_start : std_logic; error_on_new_start : std_logic ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_frame_assume is
begin
end architecture;


--******************************************************************
--Module to be replicated for cover checks
--This module is bound to the PSL vunits with cover checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_frame_cover is 
  generic (
   OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC
  );
  port(clk : std_logic; reset_n : std_logic; start_event : std_logic);
end entity;

architecture rtl of assert_frame_cover is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

architecture rtl of ovl_frame is 
  constant assert_name         : string  := "ASSERT_CHANGE";
  constant path                : string  := rtl'path_name;
  
  signal reset_n               : std_logic ;
  signal clk                   : std_logic ;
  signal ignore_new_start      : std_logic:=ovl_action_on_new_start_cmp(OVL_IGNORE_NEW_START, action_on_new_start);
  signal reset_on_new_start    : std_logic:=ovl_action_on_new_start_cmp(OVL_RESET_ON_NEW_START, action_on_new_start);
  signal error_on_new_start    : std_logic:=ovl_action_on_new_start_cmp(OVL_ERROR_ON_NEW_START, action_on_new_start);
  signal win                   : std_logic := '0';
  signal r_start_event         : std_logic := '0';


  component assert_frame_assert is 
    generic (
      min_cks          : integer   := 1; 
      max_cks          : integer   := 2;
      min_cks_resolved : integer   := 1;
      max_cks_resolved : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; start_event : std_logic ; test_expr : std_logic; win : std_logic ; ignore_new_start : std_logic ; reset_on_new_start : std_logic; error_on_new_start : std_logic ; xzcheck_enable : ovl_ctrl);
  end component;


  component assert_frame_assume is 
    generic (
      min_cks          : integer   := 1; 
      max_cks          : integer   := 2;
      min_cks_resolved : integer   := 1;
      max_cks_resolved : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; start_event : std_logic ; test_expr : std_logic; win : std_logic ; ignore_new_start : std_logic ; reset_on_new_start : std_logic; error_on_new_start : std_logic ; xzcheck_enable : ovl_ctrl);
  end component;


  component assert_frame_cover is 
    generic (
     OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC
    );
    port(clk : std_logic; reset_n : std_logic; start_event : std_logic);
  end component;


begin
 
ovl_p : process (clk)     
  variable ii       : INTEGER := 0;
begin
  if (rising_edge(clk)) then
    r_start_event <= start_event;
    if (reset_n = '0') then
      ii := 0;
      win <= '0';
    else 
      if (max_cks > 0) then
         if(win = '0') then
           if((r_start_event = '0') AND (start_event = '1') AND (test_expr /= '1')) then
              win <= '1';
              ii := max_cks;
           end if;
         else
           if((r_start_event = '0') AND (start_event = '1')  AND
              (action_on_new_start = OVL_RESET_ON_NEW_START) AND (test_expr /= '1')) then
              ii := max_cks;
           else if ((ii <= 1) OR (test_expr = '1')) then
                    win <= '0';
                else 
                    ii := ii -1;
                end if;
           end if;
         end if;
     else if (min_cks > 0) then 
             if(win = '0') then
               if((r_start_event = '0') AND (start_event = '1') AND (test_expr /= '1')) then
                  win <= '1';
                  ii := min_cks;
               end if;
             else
               if((r_start_event = '0') AND (start_event = '1')  AND
                  (action_on_new_start = OVL_RESET_ON_NEW_START) AND (test_expr /= '1')) then
                  ii := min_cks;
               else if ((ii <= 1) OR (test_expr = '1')) then
                        win <= '0';
                    else 
                        ii := ii -1;
                    end if;
               end if;
             end if;
      end if;
     end if;
  end if;
end if;
end process ovl_p;



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
  -- Assert Property
  ------------------------------------------------------------------------------ 
  ovl_assert_on_gen : if (((property_type = OVL_ASSERT) or (property_type = OVL_ASSERT_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
  assert_checks : assert_frame_assert
      generic map 
       ( min_cks => min_cks, max_cks => max_cks, min_cks_resolved=>check_condition_integer(min_cks>1, min_cks-2, 0), max_cks_resolved=>check_condition_integer(max_cks>1, max_cks-1, 1)) 
      port map 
        (clk => clk, reset_n => reset_n, start_event => start_event, test_expr => test_expr, win => win, ignore_new_start => ignore_new_start, reset_on_new_start => reset_on_new_start, error_on_new_start => error_on_new_start, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
 
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_checks : assert_frame_assume
      generic map 
       ( min_cks => min_cks, max_cks => max_cks,  min_cks_resolved=>check_condition_integer(min_cks>1, min_cks-2, 0), max_cks_resolved=>check_condition_integer(max_cks>1, max_cks-1, 1))
      port map 
        (clk => clk, reset_n => reset_n, start_event => start_event, test_expr => test_expr, win => win, ignore_new_start => ignore_new_start, reset_on_new_start => reset_on_new_start, error_on_new_start => error_on_new_start, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;

  ------------------------------------------------------------------------------
  -- Cover Property
  ------------------------------------------------------------------------------ 
  ovl_cover_on_gen : if ((coverage_level /= OVL_COVER_NONE) and (controls.cover_ctrl = OVL_ON)) generate
    cover_checks : assert_frame_cover
      generic map 
       ( OVL_COVER_BASIC_ON => coverage_level)
      port map 
        (clk => clk, reset_n => reset_n, start_event => start_event);
  end generate ovl_cover_on_gen;

end architecture rtl;
