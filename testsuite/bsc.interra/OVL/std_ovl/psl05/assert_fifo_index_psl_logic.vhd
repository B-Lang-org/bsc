-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

--******************************************************************
--Module to be replicated for assert checks
--This module is bound to the PSL vunits with assert checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_fifo_index_assert is 
  generic (
    depth                 : integer   := 1; 
    push_width            : integer   := 1;
    pop_width             : integer   := 1;
    simultaneous_push_pop : integer   := 1;
    cnt_reg_width         : integer   := 1
  );
  port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0) ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_fifo_index_assert is
begin
end architecture;


--******************************************************************
--Module to be replicated for assume checks
--This module is bound to the PSL vunits with assume checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_fifo_index_assume is 
  generic (
    depth                 : integer   := 1; 
    push_width            : integer   := 1;
    pop_width             : integer   := 1;
    simultaneous_push_pop : integer   := 1;
    cnt_reg_width         : integer   := 1
  );
  port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0) ; xzcheck_enable : ovl_ctrl);
end entity;

architecture rtl of assert_fifo_index_assume is
begin
end architecture;

--******************************************************************
--Module to be replicated for cover checks
--This module is bound to the PSL vunits with cover checks
--******************************************************************
library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity assert_fifo_index_cover is 
  generic (
    depth                 : integer   := 1; 
    push_width            : integer   := 1;
    pop_width             : integer   := 1;
    simultaneous_push_pop : integer   := 1;
    cnt_reg_width         : integer   := 1;
    OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC; 
    OVL_COVER_CORNER_ON   : integer   := OVL_COVER_CORNER 
  );
  port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0));
end entity;

architecture rtl of assert_fifo_index_cover is
begin
end architecture;


library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;
use ieee.numeric_std.all;

architecture rtl of ovl_fifo_index is 
  constant assert_name         : string  := "ASSERT_CHANGE";
  constant path                : string  := rtl'path_name;
  constant cnt_reg_width       : integer := logb2(depth +1);  

  
  signal reset_n               : std_logic;
  signal clk                   : std_logic;
  signal cnt                   : std_logic_vector(cnt_reg_width - 1 downto 0);


  component assert_fifo_index_assert is 
    generic (
      depth                 : integer   := 1; 
      push_width            : integer   := 1;
      pop_width             : integer   := 1;
      simultaneous_push_pop : integer   := 1;
      cnt_reg_width         : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0) ; xzcheck_enable : ovl_ctrl);
  end component;
  
  component assert_fifo_index_assume is 
    generic (
      depth                 : integer   := 1; 
      push_width            : integer   := 1;
      pop_width             : integer   := 1;
      simultaneous_push_pop : integer   := 1;
      cnt_reg_width         : integer   := 1
    );
    port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0) ; xzcheck_enable : ovl_ctrl);
  end component;
  
  component assert_fifo_index_cover is 
    generic (
               depth                 : integer   := 1; 
               push_width            : integer   := 1;
               pop_width             : integer   := 1;
               simultaneous_push_pop : integer   := 1;
               cnt_reg_width         : integer   := 1;
               OVL_COVER_BASIC_ON    : integer   := OVL_COVER_BASIC; 
               OVL_COVER_CORNER_ON   : integer   := OVL_COVER_CORNER 
           );
    port(clk : std_logic; reset_n : std_logic; push : std_logic_vector(push_width-1 downto 0); pop : std_logic_vector(pop_width-1 downto 0); cnt : std_logic_vector(cnt_reg_width -1 downto 0));
  end component;


begin
 
ovl_p : process (clk)     
  variable push_int : INTEGER := 0;
  variable pop_int  : INTEGER := 0;
  variable cnt_int  : INTEGER := 0;
begin
  if (rising_edge(clk)) then
    if (reset_n = '0') then
      cnt <= (others => '0');
    else
      push_int := to_integer(push(push_width -1 downto 0));
      pop_int := to_integer(pop(pop_width -1 downto 0));
      cnt_int := to_integer(cnt(cnt_reg_width -1 downto 0));

      if ( (push_int /=0) and (pop_int = 0)) then -- push
        if ( (cnt_int + push_int) <= depth) then
           cnt <= std_logic_vector(to_unsigned(cnt_int + push_int,cnt_reg_width)); 
        end if;
      else if ( (push_int =0) and (pop_int /= 0)) then -- pop
        if ( (cnt_int >= pop_int)) then
           cnt <= std_logic_vector(to_unsigned(cnt_int - pop_int,cnt_reg_width)); 
        end if;
      else if ( (push_int /=0) and (pop_int /= 0)) then -- push and pop
        if ( simultaneous_push_pop = 1) then
          if ( NOT((cnt_int + push_int - pop_int) > depth) AND NOT( (cnt_int + push_int)  < pop_int))  then
             cnt <= std_logic_vector(to_unsigned(cnt_int + push_int - pop_int,cnt_reg_width)); 
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
  assert_checks : assert_fifo_index_assert
      generic map 
       ( depth => depth, push_width => push_width, pop_width => pop_width , simultaneous_push_pop => simultaneous_push_pop , cnt_reg_width => cnt_reg_width)
      port map 
        (clk => clk, reset_n => reset_n, push => push, pop => pop, cnt => cnt, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assert_on_gen;
 
  ------------------------------------------------------------------------------
  -- Assume Property
  ------------------------------------------------------------------------------ 
  ovl_assume_on_gen : if (((property_type = OVL_ASSUME) or (property_type = OVL_ASSUME_2STATE)) and ovl_2state_is_on(controls, property_type)) generate
    assume_checks : assert_fifo_index_assume
      generic map 
       ( depth => depth, push_width => push_width, pop_width => pop_width , simultaneous_push_pop => simultaneous_push_pop , cnt_reg_width => cnt_reg_width)
      port map 
        (clk => clk, reset_n => reset_n, push => push, pop => pop, cnt => cnt, xzcheck_enable => controls.xcheck_ctrl);
  end generate ovl_assume_on_gen;

  ------------------------------------------------------------------------------
  -- Cover Property
  ------------------------------------------------------------------------------ 
  ovl_cover_on_gen : if ((coverage_level /= OVL_COVER_NONE) and (controls.cover_ctrl = OVL_ON)) generate
    cover_checks : assert_fifo_index_cover
      generic map 
       ( depth => depth, push_width => push_width, pop_width => pop_width , simultaneous_push_pop => simultaneous_push_pop , cnt_reg_width => cnt_reg_width , OVL_COVER_BASIC_ON => coverage_level , OVL_COVER_CORNER_ON => coverage_level )
      port map 
        (clk => clk, reset_n => reset_n, push => push, pop => pop, cnt => cnt);
  end generate ovl_cover_on_gen;

end architecture rtl;
