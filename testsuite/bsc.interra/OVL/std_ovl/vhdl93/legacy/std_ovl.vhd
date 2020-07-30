-- Accellera Standard V2.8.1 Open Verification Library (OVL)
-- Accellera Copyright (c) 2005-2014. All rights reserved.

LIBRARY ieee;
USE ieee.std_logic_1164.ALL;

PACKAGE std_ovl IS

  constant OVL_STD_DEFINES_H : boolean := true;
  
  constant OVL_VERSION : string := "V2.8";

  -- active edges
  constant OVL_NOEDGE  : integer := 0;
  constant OVL_POSEDGE : integer := 1;
  constant OVL_NEGEDGE : integer := 2;
  constant OVL_ANYEDGE : integer := 3;
  
  -- severity level 
  constant OVL_FATAL   : integer := 0;
  constant OVL_ERROR   : integer := 1;
  constant OVL_WARNING : integer := 2;
  constant OVL_INFO    : integer := 3;

  -- coverage levels
  constant OVL_COVER_NONE      : integer := 0;
  constant OVL_COVER_SANITY    : integer := 1;
  constant OVL_COVER_BASIC     : integer := 2;
  constant OVL_COVER_CORNER    : integer := 4;
  constant OVL_COVER_STATISTIC : integer := 8;
  constant OVL_COVER_ALL       : integer := 15; 

  -- property type
  constant OVL_ASSERT     : integer := 0;
  constant OVL_ASSUME	  : integer := 1;
  constant OVL_IGNORE	  : integer := 2;

  -- necessary condition
  constant OVL_TRIGGER_ON_MOST_PIPE    : integer := 0;
  constant OVL_TRIGGER_ON_FIRST_PIPE   : integer := 1;
  constant OVL_TRIGGER_ON_FIRST_NOPIPE : integer := 2;
  
  -- action on new start
  constant OVL_IGNORE_NEW_START : integer := 0;
  constant OVL_RESET_ON_NEW_START : integer := 1;
  constant OVL_ERROR_ON_NEW_START : integer := 2;

  -- inactive levels
  constant OVL_ALL_ZEROS : integer := 0;
  constant OVL_ALL_ONES  : integer := 1;
  constant OVL_ONE_COLD  : integer := 2;

  -- Global reset
  signal OVL_GLOBAL_RESET : boolean := false;
  signal OVL_RESET_SIGNAL : std_ulogic;

  -- End of simulation
  signal OVL_END_OF_SIMULATION : std_ulogic := '0';
  
  component assert_always
    generic (
      severity_level : integer := OVL_ERROR;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_always_on_edge
    generic (
      severity_level : integer := OVL_ERROR;
      edge_type        : integer := OVL_NOEDGE;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      sampling_event   : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_change
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      num_cks          : integer := 1;
      action_on_new_start : integer := OVL_IGNORE_NEW_START;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_cycle_sequence
    generic (
      severity_level : integer := OVL_ERROR;
      num_cks          : integer := 2;
      necessary_condition : integer := OVL_TRIGGER_ON_MOST_PIPE;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      event_sequence   : in std_ulogic_vector(num_cks-1 downto 0)
    );
  end component;

  component assert_decrement
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      value            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_delta
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      min              : integer := 1;
      max              : integer := 1;      
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_even_parity
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_fifo_index
    generic (
      severity_level : integer := OVL_ERROR;
      depth            : integer := 1;
      push_width       : integer := 1;
      pop_width        : integer := 1;      
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL;
      simultaneous_push_pop : integer := 1
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      push             : in std_ulogic_vector(push_width-1 downto 0);
      pop              : in std_ulogic_vector(pop_width-1 downto 0)
    );
  end component;

  component assert_frame
    generic (
      severity_level : integer := OVL_ERROR;
      min_cks          : integer := 0;
      max_cks          : integer := 0;
      action_on_new_start : integer := OVL_IGNORE_NEW_START;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic
      );
  end component;

  component assert_handshake
    generic (
      severity_level : integer := OVL_ERROR;
      min_ack_cycle    : integer := 0;
      max_ack_cycle    : integer := 0;
      req_drop         : integer := 0;
      deassert_count   : integer := 0;
      max_ack_length   : integer := 0;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      req              : in std_ulogic;
      ack              : in std_ulogic
      );
  end component;

  component assert_implication
    generic (
      severity_level : integer := OVL_ERROR;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      antecedent_expr  : in std_ulogic;
      consequent_expr  : in std_ulogic
    );
  end component;

  component assert_increment
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      value            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_never
    generic (
      severity_level : integer := OVL_ERROR;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_never_unknown
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      qualifier        : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_never_unknown_async
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_next
    generic (
      severity_level : integer := OVL_ERROR;
      num_cks          : integer := 1;
      check_overlapping : integer := 1;
      check_missing_start : integer := 0;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_no_overflow
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      min              : integer := 0;
      max              : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_no_transition
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0);
      start_state      : in std_ulogic_vector(width-1 downto 0);
      next_state       : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_no_underflow
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      min              : integer := 0;
      max              : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_odd_parity
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_one_cold
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 32;
      inactive         : integer := OVL_ONE_COLD;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_one_hot
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 32;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_proposition
    generic (
      severity_level : integer := OVL_ERROR;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_quiescent_state
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      state_expr       : in std_ulogic_vector(width-1 downto 0);
      check_value      : in std_ulogic_vector(width-1 downto 0);
      sample_event     : in std_ulogic
    );
  end component;

  component assert_range
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      min              : integer := 1;
      max              : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_time
    generic (
      severity_level : integer := OVL_ERROR;
      num_cks          : integer := 1;
      action_on_new_start : integer := OVL_IGNORE_NEW_START;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic
      );
  end component;

  component assert_transition
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0);
      start_state      : in std_ulogic_vector(width-1 downto 0);
      next_state       : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

  component assert_unchange
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      num_cks          : integer := 1;
      action_on_new_start : integer := OVL_IGNORE_NEW_START;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

 component assert_width
    generic (
      severity_level : integer := OVL_ERROR;
      min_cks          : integer := 1;
      max_cks          : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic
    );
  end component;

  component assert_win_change
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0);
      end_event        : in std_ulogic
    );
  end component;

  component assert_win_unchange
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 1;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0);
      end_event        : in std_ulogic
    );
  end component;

  component assert_window
    generic (
      severity_level : integer := OVL_ERROR;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      start_event      : in std_ulogic;
      test_expr        : in std_ulogic;
      end_event        : in std_ulogic
    );
  end component;

  component assert_zero_one_hot
    generic (
      severity_level : integer := OVL_ERROR;
      width            : integer := 32;
      property_type    : integer := OVL_ASSERT;
      msg              : string  := "VIOLATION";
      coverage_level   : integer := OVL_COVER_ALL
    );
    port (
      clk              : in std_ulogic;
      reset_n          : in std_ulogic;
      test_expr        : in std_ulogic_vector(width-1 downto 0)
    );
  end component;

END std_ovl;
