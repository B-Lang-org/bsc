-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_cycle_sequence_assert is 
  generic (
    num_cks             : integer                 := 2; 
    necessary_condition : integer                 := 0 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0); xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_cycle_sequence_assert is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_cycle_sequence_assume is 
  generic (
    num_cks             : integer                 := 2; 
    necessary_condition : integer                 := 0 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0); xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_cycle_sequence_assume is
begin
end architecture;

--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_cycle_sequence_cover is 
  generic (
    num_cks             : integer                 := 4; 
    necessary_condition : integer                 := 0; 
    OVL_COVER_BASIC_ON  : integer                 := 1 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0));
end entity;

architecture rtl of assert_cycle_sequence_cover is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;

architecture rtl of ovl_cycle_sequence is 
  constant assert_name         : string := "ASSERT_CHANGE";
  constant path        : string := rtl'path_name;

  constant NUM_CKS_1   : integer := (num_cks-1);
  
  signal reset_n       : std_logic;
  signal clk           : std_logic;
  signal seq_queue     : std_logic_vector(num_cks - 1 downto 0);


component assert_cycle_sequence_assert is 
  generic (
    num_cks             : integer                 := 2; 
    necessary_condition : integer                 := 0 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0); xzcheck_enable : ovl_ctrl);
end component;

component assert_cycle_sequence_assume is 
  generic (
    num_cks             : integer                 := 2; 
    necessary_condition : integer                 := 0 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0); xzcheck_enable : ovl_ctrl);
end component;

component assert_cycle_sequence_cover is 
  generic (
    num_cks             : integer                 := 4; 
    necessary_condition : integer                 := 0; 
    OVL_COVER_BASIC_ON  : integer                 := 1 
  );
  port(clk : std_logic; reset_n : std_logic; event_sequence : std_logic_vector(num_cks-1 downto 0); seq_queue : std_logic_vector(num_cks-1 downto 0));
end component;

begin
 
ovl_p : process (clk)     
  variable seq_queue_shifted : std_logic_vector(num_cks - 1 downto 0);
begin
  if (rising_edge(clk)) then
    if (reset_n = '0') then
      seq_queue <= (others => '0');
    else
      if (necessary_condition = OVL_TRIGGER_ON_FIRST_NOPIPE) then
        seq_queue(NUM_CKS_1) <= ((not(or_reduce(seq_queue(NUM_CKS_1 downto 1)))) and (event_sequence(NUM_CKS_1)));
      else  
        seq_queue(NUM_CKS_1) <= event_sequence(NUM_CKS_1);
      end if;
      
      if (NUM_CKS_1 > 0) then
	seq_queue_shifted := seq_queue srl 1;
        seq_queue(NUM_CKS_1 -1 downto 0) <= ((seq_queue_shifted(NUM_CKS_1 -1 downto 0)) and event_sequence(NUM_CKS_1 -1  downto 0)); --NUM_CKS_1-1
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
  assert_checks : assert_cycle_sequence_assert
     generic map 
       ( num_cks => num_cks, necessary_condition => necessary_condition)
      port map 
        (clk => clk, reset_n => reset_n, event_sequence => event_sequence, seq_queue => seq_queue, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
 
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_checks : assert_cycle_sequence_assume
     generic map 
       ( num_cks => num_cks, necessary_condition => necessary_condition)
      port map 
        (clk => clk, reset_n => reset_n, event_sequence => event_sequence, seq_queue => seq_queue, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;

  ------------------------------------------------------------------------------
  -- Cover Property
  ------------------------------------------------------------------------------ 
  ovl_cover_on_gen : if ((coverage_level /= OVL_COVER_NONE) and (controls.cover_ctrl = OVL_ON)) generate
    cover_checks : assert_cycle_sequence_cover
     generic map (
       num_cks => num_cks, 
       necessary_condition => necessary_condition, 
       OVL_COVER_BASIC_ON => coverage_level )
      port map 
        (clk => clk, reset_n => reset_n, event_sequence => event_sequence, seq_queue => seq_queue);
  end generate ovl_cover_on_gen;

end architecture rtl;

