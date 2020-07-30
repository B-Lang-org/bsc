-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

package std_ovl_vhdl_components is

  ------------------------------------------------------------------------------
  -- ovl_always
  ------------------------------------------------------------------------------
  component ovl_always
    generic (
      severity_level      : ovl_severity_level      := OVL_SEVERITY_LEVEL_NOT_SET;  
      property_type       : ovl_property_type       := OVL_PROPERTY_TYPE_NOT_SET;  
      msg                 : string                  := OVL_MSG_NOT_SET;       
      coverage_level      : ovl_coverage_level      := OVL_COVERAGE_LEVEL_NOT_SET;     
      clock_edge          : ovl_active_edges        := OVL_ACTIVE_EDGES_NOT_SET;      
      reset_polarity      : ovl_reset_polarity      := OVL_RESET_POLARITY_NOT_SET;    
      gating_type         : ovl_gating_type         := OVL_GATING_TYPE_NOT_SET;      
      controls            : ovl_ctrl_record         := OVL_CTRL_DEFAULTS      
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic;
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_always;

  ------------------------------------------------------------------------------
  -- ovl_never
  ------------------------------------------------------------------------------
  component ovl_never
    generic (
      severity_level      : ovl_severity_level      := OVL_SEVERITY_LEVEL_NOT_SET;  
      property_type       : ovl_property_type       := OVL_PROPERTY_TYPE_NOT_SET;  
      msg                 : string                  := OVL_MSG_NOT_SET;       
      coverage_level      : ovl_coverage_level      := OVL_COVERAGE_LEVEL_NOT_SET;     
      clock_edge          : ovl_active_edges        := OVL_ACTIVE_EDGES_NOT_SET;      
      reset_polarity      : ovl_reset_polarity      := OVL_RESET_POLARITY_NOT_SET;    
      gating_type         : ovl_gating_type         := OVL_GATING_TYPE_NOT_SET;      
      controls            : ovl_ctrl_record         := OVL_CTRL_DEFAULTS      
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic;
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_never;

  ------------------------------------------------------------------------------
  -- ovl_next
  ------------------------------------------------------------------------------
  component ovl_next
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      num_cks             : positive           := 1;
      check_overlapping   : ovl_chk_overlap    := OVL_CHK_OVERLAP_OFF;
      check_missing_start : ovl_ctrl           := OVL_OFF;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      start_event         : in  std_logic;
      test_expr           : in  std_logic;
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_next;

  ------------------------------------------------------------------------------
  -- ovl_cycle_sequence
  ------------------------------------------------------------------------------
  component ovl_cycle_sequence
    generic (
      severity_level      : ovl_severity_level      := OVL_SEVERITY_LEVEL_NOT_SET;
      num_cks             : ovl_positive_2          := 2;
      necessary_condition : ovl_necessary_condition := OVL_TRIGGER_ON_MOST_PIPE;
      property_type       : ovl_property_type       := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string                  := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level      := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges        := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity      := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type         := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      event_sequence      : in  std_logic_vector(num_cks        - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_cycle_sequence;

  ------------------------------------------------------------------------------
  -- ovl_zero_one_hot
  ------------------------------------------------------------------------------
  component ovl_zero_one_hot
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width               : positive           := 32;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic_vector(width          - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_zero_one_hot;

  ------------------------------------------------------------------------------
  -- ovl_range
  ------------------------------------------------------------------------------
  component ovl_range
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width               : positive           := 1;
      min                 : natural            := 0;
      max                 : natural            := 1;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic_vector(width          - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_range;

  ------------------------------------------------------------------------------
  -- ovl_one_hot
  ------------------------------------------------------------------------------
  component ovl_one_hot
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width               : positive           := 32;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic_vector(width          - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_one_hot;

  ------------------------------------------------------------------------------
  -- ovl_never_unknown
  ------------------------------------------------------------------------------
  component ovl_never_unknown
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width               : positive           := 1;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock               : in  std_logic;
      reset               : in  std_logic;
      enable              : in  std_logic;
      qualifier           : in  std_logic;
      test_expr           : in  std_logic_vector(width          - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_never_unknown;

  ------------------------------------------------------------------------------
  -- ovl_never_unknown_async
  ------------------------------------------------------------------------------
  component ovl_never_unknown_async
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width               : positive           := 1;
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg                 : string             := OVL_MSG_NOT_SET;
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;    
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      reset               : in  std_logic;
      enable              : in  std_logic;
      test_expr           : in  std_logic_vector(width          - 1 downto 0);
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_never_unknown_async;

  ------------------------------------------------------------------------------
  -- ovl_implication
  ------------------------------------------------------------------------------
  component ovl_implication
    generic (
      severity_level      : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;    
      property_type       : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;     
      msg                 : string             := OVL_MSG_NOT_SET;               
      coverage_level      : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;    
      clock_edge          : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;      
      reset_polarity      : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;    
      gating_type         : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;      
      controls            : ovl_ctrl_record    := OVL_CTRL_DEFAULTS              
    );
    port (
      clock               : in  std_logic;                                       
      reset               : in  std_logic;                                       
      enable              : in  std_logic;
      antecedent_expr     : in  std_logic;                                       
      consequent_expr     : in  std_logic;                                       
      fire                : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)  
    );
  end component ovl_implication;



  ------------------------------------------------------------------------------
  -- ovl_always_on_edge
  ------------------------------------------------------------------------------
  component ovl_always_on_edge
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      edge_type            : natural                 := OVL_NOEDGE;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      sampling_event       : in  std_logic;
      test_expr            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_always_on_edge;

  ------------------------------------------------------------------------------
  -- ovl_change
  ------------------------------------------------------------------------------
  component ovl_change
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      num_cks              : natural                 := 1;
      action_on_new_start  : natural                 := OVL_ACTION_ON_NEW_START_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_change;

  ------------------------------------------------------------------------------
  -- ovl_decrement
  ------------------------------------------------------------------------------
  component ovl_decrement
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      value                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_decrement;

  ------------------------------------------------------------------------------
  -- ovl_delta
  ------------------------------------------------------------------------------
  component ovl_delta
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      min                  : natural                 := 1;
      max                  : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_delta;

  ------------------------------------------------------------------------------
  -- ovl_even_parity
  ------------------------------------------------------------------------------
  component ovl_even_parity
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_even_parity;

  ------------------------------------------------------------------------------
  -- ovl_fifo_index
  ------------------------------------------------------------------------------
  component ovl_fifo_index
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      depth                : natural                 := 1;
      push_width           : natural                 := 1;
      pop_width            : natural                 := 1;
      simultaneous_push_pop: natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      push                 : in  std_logic_vector(push_width     - 1 downto 0);
      pop                  : in  std_logic_vector(pop_width      - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_fifo_index;

  ------------------------------------------------------------------------------
  -- ovl_frame
  ------------------------------------------------------------------------------
  component ovl_frame
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      min_cks              : natural                 := 0;
      max_cks              : natural                 := 0;
      action_on_new_start  : natural                 := OVL_ACTION_ON_NEW_START_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_frame;

  ------------------------------------------------------------------------------
  -- ovl_handshake
  ------------------------------------------------------------------------------
  component ovl_handshake
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      min_ack_cycle        : natural                 := 0;
      max_ack_cycle        : natural                 := 0;
      req_drop             : natural                 := 0;
      deassert_count       : natural                 := 0;
      max_ack_length       : natural                 := 0;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      req                  : in  std_logic;
      ack                  : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_handshake;

  ------------------------------------------------------------------------------
  -- ovl_increment
  ------------------------------------------------------------------------------
  component ovl_increment
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      value                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_increment;

  ------------------------------------------------------------------------------
  -- ovl_no_overflow
  ------------------------------------------------------------------------------
  component ovl_no_overflow
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      min                  : natural                 := 0;
      max                  : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_no_overflow;

  ------------------------------------------------------------------------------
  -- ovl_no_transition
  ------------------------------------------------------------------------------
  component ovl_no_transition
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      start_state          : in  std_logic_vector(width          - 1 downto 0);
      next_state           : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_no_transition;

  ------------------------------------------------------------------------------
  -- ovl_no_underflow
  ------------------------------------------------------------------------------
  component ovl_no_underflow
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      min                  : natural                 := 0;
      max                  : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_no_underflow;

  ------------------------------------------------------------------------------
  -- ovl_odd_parity
  ------------------------------------------------------------------------------
  component ovl_odd_parity
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_odd_parity;

  ------------------------------------------------------------------------------
  -- ovl_one_cold
  ------------------------------------------------------------------------------
  component ovl_one_cold
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 32;
      inactive             : natural                 := OVL_INACTIVE_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_one_cold;

  ------------------------------------------------------------------------------
  -- ovl_proposition
  ------------------------------------------------------------------------------
  component ovl_proposition
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_proposition;

  ------------------------------------------------------------------------------
  -- ovl_quiescent_state
  ------------------------------------------------------------------------------
  component ovl_quiescent_state
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      state_expr           : in  std_logic_vector(width          - 1 downto 0);
      check_value          : in  std_logic_vector(width          - 1 downto 0);
      sample_event         : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_quiescent_state;

  ------------------------------------------------------------------------------
  -- ovl_time
  ------------------------------------------------------------------------------
  component ovl_time
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      num_cks              : natural                 := 1;
      action_on_new_start  : natural                 := OVL_ACTION_ON_NEW_START_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_time;

  ------------------------------------------------------------------------------
  -- ovl_transition
  ------------------------------------------------------------------------------
  component ovl_transition
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      start_state          : in  std_logic_vector(width          - 1 downto 0);
      next_state           : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_transition;

  ------------------------------------------------------------------------------
  -- ovl_unchange
  ------------------------------------------------------------------------------
  component ovl_unchange
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      num_cks              : natural                 := 1;
      action_on_new_start  : natural                 := OVL_ACTION_ON_NEW_START_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_unchange;

  ------------------------------------------------------------------------------
  -- ovl_width
  ------------------------------------------------------------------------------
  component ovl_width
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      min_cks              : natural                 := 1;
      max_cks              : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      test_expr            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_width;

  ------------------------------------------------------------------------------
  -- ovl_win_change
  ------------------------------------------------------------------------------
  component ovl_win_change
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      end_event            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_win_change;

  ------------------------------------------------------------------------------
  -- ovl_window
  ------------------------------------------------------------------------------
  component ovl_window
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic;
      end_event            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_window;

  ------------------------------------------------------------------------------
  -- ovl_win_unchange
  ------------------------------------------------------------------------------
  component ovl_win_unchange
    generic (
      severity_level       : ovl_severity_level      := OVL_SEVERITY_DEFAULT;
      width                : natural                 := 1;
      property_type        : ovl_property_type       := OVL_PROPERTY_DEFAULT;
      msg                  : string                  := OVL_MSG_DEFAULT;
      coverage_level       : ovl_coverage_level      := OVL_COVER_DEFAULT;
      clock_edge           : ovl_active_edges        := OVL_CLOCK_EDGE_DEFAULT;
      reset_polarity       : ovl_reset_polarity      := OVL_RESET_POLARITY_DEFAULT;
      gating_type          : ovl_gating_type         := OVL_GATING_TYPE_DEFAULT;
      controls             : ovl_ctrl_record         := OVL_CTRL_DEFAULTS
    );
    port (
      clock                : in  std_logic;
      reset                : in  std_logic;
      enable               : in  std_logic;
      start_event          : in  std_logic;
      test_expr            : in  std_logic_vector(width          - 1 downto 0);
      end_event            : in  std_logic;
      fire                 : out std_logic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_win_unchange;
end package std_ovl_vhdl_components;
