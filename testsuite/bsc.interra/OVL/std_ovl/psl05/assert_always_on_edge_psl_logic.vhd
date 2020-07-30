-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
entity assert_always_on_edge_assert is 
               port( clk : std_logic; reset_n : std_logic; test_expr : std_logic; sampling_event : std_logic; 
                     noedge_type : std_logic; posedge_type : std_logic; negedge_type : std_logic; 
                     anyedge_type : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_always_on_edge_assert is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
entity assert_always_on_edge_assume is 
               port( clk : std_logic; reset_n : std_logic; test_expr : std_logic; sampling_event : std_logic; 
                     noedge_type : std_logic; posedge_type : std_logic; negedge_type : std_logic; 
                     anyedge_type : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_always_on_edge_assume is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_always_on_edge is 
  constant assert_name         : string := "OVL_ALWAYS_ON_EDGE";
  constant path                : string := rtl'path_name;
  
  signal reset_n               : std_logic;
  signal clk                   : std_logic;

  signal noedge_type           : std_logic := '0';
  signal posedge_type          : std_logic := '0';
  signal negedge_type          : std_logic := '0';
  signal anyedge_type          : std_logic := '0';

  component assert_always_on_edge_assert is 
               port( clk : std_logic; reset_n : std_logic; test_expr : std_logic; sampling_event : std_logic; 
                     noedge_type : std_logic; posedge_type : std_logic; negedge_type : std_logic; 
                     anyedge_type : std_logic; xzcheck_enable : ovl_ctrl);
  end component;

  component assert_always_on_edge_assume is 
               port( clk : std_logic; reset_n : std_logic; test_expr : std_logic; sampling_event : std_logic; 
                     noedge_type : std_logic; posedge_type : std_logic; negedge_type : std_logic; 
                     anyedge_type : std_logic; xzcheck_enable : ovl_ctrl);
  end component;

begin
  
process(clk)
begin
   if(clk='1' and clk'event) then
       C1: case edge_type is
        when OVL_NOEDGE  => noedge_type  <= '1';
        when OVL_POSEDGE => posedge_type <= '1';
        when OVL_NEGEDGE => negedge_type <= '1';
        when OVL_ANYEDGE => anyedge_type <= '1';
        when others      => noedge_type  <= '0';
                            posedge_type <= '0';
                            negedge_type <= '0';
                            anyedge_type <= '0';
       end case C1;
   end if;
end process;

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

  assert_always_on_edge : assert_always_on_edge_assert
      port map 
        ( clk => clk, reset_n => reset_n, test_expr => test_expr, sampling_event => sampling_event, 
          noedge_type  => noedge_type, posedge_type => posedge_type, negedge_type => negedge_type,
          anyedge_type => anyedge_type, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
  
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_always_on_edge : assert_always_on_edge_assume
      port map 
        ( clk => clk, reset_n => reset_n, test_expr => test_expr, sampling_event => sampling_event, 
          noedge_type  => noedge_type, posedge_type => posedge_type, negedge_type => negedge_type,
          anyedge_type => anyedge_type, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;
    
end architecture rtl;

