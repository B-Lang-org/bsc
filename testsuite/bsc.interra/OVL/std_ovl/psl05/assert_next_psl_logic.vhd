-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_next_assert is 
  generic (
    num_cks               : positive   := 1; 
    check_overlapping     : integer   := 1;
    check_missing_start   : integer   := 1
  );
  port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start: std_logic; no_overlapping: std_logic ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_next_assert is
begin
end architecture;

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_next_assume is 
  generic (
    num_cks               : positive   := 1; 
    check_overlapping     : integer   := 1;
    check_missing_start   : integer   := 1
  );
  port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start: std_logic;no_overlapping: std_logic ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_next_assume is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_next_cover is 
  generic (
    OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC; 
    OVL_COVER_CORNER_ON   : integer   := OVL_COVER_CORNER 
  );
  port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start:  std_logic;no_overlapping: std_logic);
end entity;

architecture rtl of assert_next_cover is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

architecture rtl of ovl_next is 
  constant assert_name         : string  := "ASSERT_CHANGE";
  constant path                : string  := rtl'path_name;
  
  signal reset_n               : std_logic;
  signal clk                   : std_logic;
  signal i,j                   : integer;
  signal check,start_value,r   : std_logic;
  signal value_in_last_cycle   : std_logic_vector(num_cks-1 downto 0);

  component assert_next_assert is 
    generic (
      num_cks               : positive   := 1; 
      check_overlapping     : integer   := 1;
      check_missing_start   : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start: std_logic;  no_overlapping: std_logic ; xzcheck_enable : ovl_ctrl);
  end component;


  component assert_next_assume is 
    generic (
      num_cks               : positive   := 1; 
      check_overlapping     : integer   := 1;
      check_missing_start   : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start: std_logic;  no_overlapping: std_logic ; xzcheck_enable : ovl_ctrl);
  end component;

  component assert_next_cover is 
    generic (
               OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC; 
               OVL_COVER_CORNER_ON   : integer   := OVL_COVER_CORNER 
            );
    port(clk : std_logic; reset_n : std_logic; test_expr : std_logic; start_event : std_logic; prev_start: std_logic;  no_overlapping: std_logic);
  end component;

begin
 
ovl_p : process (clk)     
begin
  if (rising_edge(clk)) then
    if (reset_n = '0') then
      i  <= 0;
      check <= '1';  
    else
      if(start_event = '1') then
         i <= num_cks;
         if(num_cks <=0) then
           check <= '1';
         else
           check <= '0';
         end if;
      else if ( i > 1) then
              i <= i -1;
              if( i <=0) then
                check <= '1';
              else
                check <= '0';
              end if;  
          end if;
       end if;
    end if;
 end if;
end process ovl_p;

previous_start_determination: process(clk, start_event)
begin
  if(clk='1' and clk'event) then
    if(start_event='0') then
	value_in_last_cycle(0)<='0';
	else value_in_last_cycle(0)<='1';
    end if;
    for j in 1 to num_cks-1 loop
	if(value_in_last_cycle(j-1)='0' or value_in_last_cycle(j-1)='1') then
	value_in_last_cycle(j)<= value_in_last_cycle(j-1);
	end if;
	
    end loop;
    start_value <= value_in_last_cycle(num_cks-1);
  end if;
end process previous_start_determination;
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
  assert_checks : assert_next_assert
      generic map 
       ( num_cks => num_cks-1, check_overlapping => check_overlapping, check_missing_start => check_missing_start) --num_cks-1 because generic call not supported in repetition operator(PSL FILE)
      port map 
        (clk => clk, reset_n => reset_n, test_expr => test_expr, start_event => start_event, prev_start=>start_value, no_overlapping => check, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
 
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_checks : assert_next_assume
      generic map 
       ( num_cks => num_cks-1, check_overlapping => check_overlapping, check_missing_start => check_missing_start)
      port map 
        (clk => clk, reset_n => reset_n, test_expr => test_expr, start_event => start_event, prev_start=>start_value,no_overlapping => check, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;

  ------------------------------------------------------------------------------
  -- Cover Property
  ------------------------------------------------------------------------------ 
  ovl_cover_on_gen : if ((coverage_level /= OVL_COVER_NONE) and (controls.cover_ctrl = OVL_ON)) generate
    cover_checks : assert_next_cover
      generic map 
       ( OVL_COVER_BASIC_ON => coverage_level, OVL_COVER_CORNER_ON => coverage_level)
      port map 
        (clk => clk, reset_n => reset_n, test_expr => test_expr, start_event => start_event, prev_start=>start_value,no_overlapping => check);
  end generate ovl_cover_on_gen;

end architecture rtl;
