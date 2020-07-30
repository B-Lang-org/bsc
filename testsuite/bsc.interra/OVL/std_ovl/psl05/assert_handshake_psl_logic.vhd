-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_handshake_assert is 
  generic (
    min_ack_cycle       : integer  := 0; 
    max_ack_cycle       : integer  := 0; 
    req_drop            : integer  := 0; 
    deassert_count      : integer  := 0; 
    max_ack_length      : integer  := 0
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic; first_req : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_handshake_assert is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_handshake_assume is 
  generic (
    min_ack_cycle       : integer  := 0; 
    max_ack_cycle       : integer  := 0; 
    req_drop            : integer  := 0; 
    deassert_count      : integer  := 0; 
    max_ack_length      : integer  := 0
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic; first_req : std_logic; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_handshake_assume is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_handshake_cover is 
  generic (
    OVL_COVER_BASIC_ON  : integer  := 1
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic);
end entity;

architecture rtl of assert_handshake_cover is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_handshake is 
  constant assert_name         : string := "OVL_HANDSHAKE";
  constant path                : string := rtl'path_name;
  
  signal reset_n               : std_logic;
  signal clk                   : std_logic;
  
  signal first_req             : std_logic;

component assert_handshake_assert is 
  generic (
    min_ack_cycle       : integer  := 0; 
    max_ack_cycle       : integer  := 0; 
    req_drop            : integer  := 0; 
    deassert_count      : integer  := 0; 
    max_ack_length      : integer  := 0
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic; first_req : std_logic; xzcheck_enable : ovl_ctrl);
end component;

component assert_handshake_assume is 
  generic (
    min_ack_cycle       : integer  := 0; 
    max_ack_cycle       : integer  := 0; 
    req_drop            : integer  := 0; 
    deassert_count      : integer  := 0; 
    max_ack_length      : integer  := 0
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic; first_req : std_logic; xzcheck_enable : ovl_ctrl);
end component;

component assert_handshake_cover is 
  generic (
    OVL_COVER_BASIC_ON  : integer  := 1
  );
  port(clk : std_logic; reset_n : std_logic; req : std_logic; ack : std_logic);
end component;

begin

ovl_p : process (clk)     
begin
  if (rising_edge(clk)) then
    if (reset_n /= '0') then
      if ((first_req xor first_req) = '0') then
        if (req = '1') then
          first_req <= '1';
        end if;
      else
        first_req <= '0';
      end if;
    else 
      first_req <= '0';
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

  assert_checks : assert_handshake_assert
     generic map 
       (  min_ack_cycle   => min_ack_cycle
          ,max_ack_cycle  => max_ack_cycle     
          ,req_drop       => req_drop      
          ,deassert_count => deassert_count
          ,max_ack_length => max_ack_length
       )
      port map 
        (clk => clk, reset_n => reset_n, req => req, ack => ack, first_req => first_req, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
 
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_checks : assert_handshake_assume
     generic map 
       (  min_ack_cycle   => min_ack_cycle
          ,max_ack_cycle  => max_ack_cycle     
          ,req_drop       => req_drop      
          ,deassert_count => deassert_count
          ,max_ack_length => max_ack_length
       )
      port map 
        (clk => clk, reset_n => reset_n, req => req, ack => ack, first_req => first_req, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;

  ------------------------------------------------------------------------------
  -- Cover Property
  ------------------------------------------------------------------------------ 
  ovl_cover_on_gen : if ((coverage_level /= OVL_COVER_NONE) and (controls.cover_ctrl = OVL_ON)) generate
    cover_checks : assert_handshake_cover
     generic map (
       OVL_COVER_BASIC_ON => coverage_level)
      port map 
        (clk => clk, reset_n => reset_n, req => req, ack => ack);
  end generate ovl_cover_on_gen;

end architecture rtl;



