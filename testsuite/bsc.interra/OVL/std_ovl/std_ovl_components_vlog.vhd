-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

package std_ovl_components is

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
end package std_ovl_components;

------------------------------------------------------------------------------
-- ovl_always_on_edge
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_always_on_edge is
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
end entity ovl_always_on_edge;

architecture str of ovl_always_on_edge is
  signal sampling_event_d_1 : std_logic;
  signal sampling_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
begin
  sampling_event_d_1 <= sampling_event;
  sampling_event_d_2 <= sampling_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_always_on_edge
    generic map (
      severity_level          => severity_level,
      edge_type               => edge_type,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      sampling_event          => sampling_event_d_2,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_change
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_change is
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
end entity ovl_change;

architecture str of ovl_change is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_change
    generic map (
      severity_level          => severity_level,
      width                   => width,
      num_cks                 => num_cks,
      action_on_new_start     => action_on_new_start,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_decrement
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_decrement is
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
end entity ovl_decrement;

architecture str of ovl_decrement is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_decrement
    generic map (
      severity_level          => severity_level,
      width                   => width,
      value                   => value,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_delta
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_delta is
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
end entity ovl_delta;

architecture str of ovl_delta is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_delta
    generic map (
      severity_level          => severity_level,
      width                   => width,
      min                     => min,
      max                     => max,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_even_parity
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog; 
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;
entity ovl_even_parity is
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
end entity ovl_even_parity;

architecture str of ovl_even_parity is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_even_parity
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_fifo_index
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_fifo_index is
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
end entity ovl_fifo_index;

architecture str of ovl_fifo_index is
  signal push_d_1        : std_logic_vector(push_width - 1 downto 0);
  signal push_d_2        : std_logic_vector(push_width - 1 downto 0);
  signal pop_d_1         : std_logic_vector(pop_width - 1 downto 0);
  signal pop_d_2         : std_logic_vector(pop_width - 1 downto 0);
begin
  push_d_1        <= push;
  push_d_2        <= push_d_1;
  pop_d_1         <= pop;
  pop_d_2         <= pop_d_1;

  u : entity accellera_ovl_vlog.ovl_fifo_index
    generic map (
      severity_level          => severity_level,
      depth                   => depth,
      push_width              => push_width,
      pop_width               => pop_width,
      simultaneous_push_pop   => simultaneous_push_pop,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      push                    => push_d_2,
      pop                     => pop_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_frame
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_frame is
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
end entity ovl_frame;

architecture str of ovl_frame is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_frame
    generic map (
      severity_level          => severity_level,
      min_cks                 => min_cks,
      max_cks                 => max_cks,
      action_on_new_start     => action_on_new_start,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_handshake
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_handshake is
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
end entity ovl_handshake;

architecture str of ovl_handshake is
  signal req_d_1         : std_logic;
  signal req_d_2         : std_logic;
  signal ack_d_1         : std_logic;
  signal ack_d_2         : std_logic;
begin
  req_d_1         <= req;
  req_d_2         <= req_d_1;
  ack_d_1         <= ack;
  ack_d_2         <= ack_d_1;

  u : entity accellera_ovl_vlog.ovl_handshake
    generic map (
      severity_level          => severity_level,
      min_ack_cycle           => min_ack_cycle,
      max_ack_cycle           => max_ack_cycle,
      req_drop                => req_drop,
      deassert_count          => deassert_count,
      max_ack_length          => max_ack_length,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      req                     => req_d_2,
      ack                     => ack_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_increment
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_increment is
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
end entity ovl_increment;

architecture str of ovl_increment is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_increment
    generic map (
      severity_level          => severity_level,
      width                   => width,
      value                   => value,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_no_overflow
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_no_overflow is
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
end entity ovl_no_overflow;

architecture str of ovl_no_overflow is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_no_overflow
    generic map (
      severity_level          => severity_level,
      width                   => width,
      min                     => min,
      --max                     => max,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_no_transition
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_no_transition is
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
end entity ovl_no_transition;

architecture str of ovl_no_transition is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
  signal start_state_d_1 : std_logic_vector(width - 1 downto 0);
  signal start_state_d_2 : std_logic_vector(width - 1 downto 0);
  signal next_state_d_1  : std_logic_vector(width - 1 downto 0);
  signal next_state_d_2  : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;
  start_state_d_1 <= start_state;
  start_state_d_2 <= start_state_d_1;
  next_state_d_1  <= next_state;
  next_state_d_2  <= next_state_d_1;

  u : entity accellera_ovl_vlog.ovl_no_transition
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      start_state             => start_state_d_2,
      next_state              => next_state_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_no_underflow
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_no_underflow is
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
end entity ovl_no_underflow;

architecture str of ovl_no_underflow is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_no_underflow
    generic map (
      severity_level          => severity_level,
      width                   => width,
      min                     => min,
      --max                     => max,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_odd_parity
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_odd_parity is
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
end entity ovl_odd_parity;

architecture str of ovl_odd_parity is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_odd_parity
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_one_cold
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_one_cold is
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
end entity ovl_one_cold;

architecture str of ovl_one_cold is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_one_cold
    generic map (
      severity_level          => severity_level,
      width                   => width,
      inactive                => inactive,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_proposition
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_proposition is
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
end entity ovl_proposition;

architecture str of ovl_proposition is
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_proposition
    generic map (
      severity_level          => severity_level,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_quiescent_state
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_quiescent_state is
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
end entity ovl_quiescent_state;

architecture str of ovl_quiescent_state is
  signal state_expr_d_1  : std_logic_vector(width - 1 downto 0);
  signal state_expr_d_2  : std_logic_vector(width - 1 downto 0);
  signal check_value_d_1 : std_logic_vector(width - 1 downto 0);
  signal check_value_d_2 : std_logic_vector(width - 1 downto 0);
  signal sample_event_d_1 : std_logic;
  signal sample_event_d_2 : std_logic;
begin
  state_expr_d_1  <= state_expr;
  state_expr_d_2  <= state_expr_d_1;
  check_value_d_1 <= check_value;
  check_value_d_2 <= check_value_d_1;
  sample_event_d_1 <= sample_event;
  sample_event_d_2 <= sample_event_d_1;

  u : entity accellera_ovl_vlog.ovl_quiescent_state
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      state_expr              => state_expr_d_2,
      check_value             => check_value_d_2,
      sample_event            => sample_event_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_time
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_time is
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
end entity ovl_time;

architecture str of ovl_time is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_time
    generic map (
      severity_level          => severity_level,
      num_cks                 => num_cks,
      action_on_new_start     => action_on_new_start,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_transition
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_transition is
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
end entity ovl_transition;

architecture str of ovl_transition is
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
  signal start_state_d_1 : std_logic_vector(width - 1 downto 0);
  signal start_state_d_2 : std_logic_vector(width - 1 downto 0);
  signal next_state_d_1  : std_logic_vector(width - 1 downto 0);
  signal next_state_d_2  : std_logic_vector(width - 1 downto 0);
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;
  start_state_d_1 <= start_state;
  start_state_d_2 <= start_state_d_1;
  next_state_d_1  <= next_state;
  next_state_d_2  <= next_state_d_1;

  u : entity accellera_ovl_vlog.ovl_transition
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      start_state             => start_state_d_2,
      next_state              => next_state_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_unchange
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_unchange is
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
end entity ovl_unchange;

architecture str of ovl_unchange is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_unchange
    generic map (
      severity_level          => severity_level,
      width                   => width,
      num_cks                 => num_cks,
      action_on_new_start     => action_on_new_start,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_width
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_width is
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
end entity ovl_width;

architecture str of ovl_width is
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
begin
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;

  u : entity accellera_ovl_vlog.ovl_width
    generic map (
      severity_level          => severity_level,
      min_cks                 => min_cks,
      max_cks                 => max_cks,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_win_change
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_win_change is
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
end entity ovl_win_change;

architecture str of ovl_win_change is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
  signal end_event_d_1   : std_logic;
  signal end_event_d_2   : std_logic;
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;
  end_event_d_1   <= end_event;
  end_event_d_2   <= end_event_d_1;

  u : entity accellera_ovl_vlog.ovl_win_change
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      end_event               => end_event_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_window
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_window is
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
end entity ovl_window;

architecture str of ovl_window is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic;
  signal test_expr_d_2   : std_logic;
  signal end_event_d_1   : std_logic;
  signal end_event_d_2   : std_logic;
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;
  end_event_d_1   <= end_event;
  end_event_d_2   <= end_event_d_1;

  u : entity accellera_ovl_vlog.ovl_window
    generic map (
      severity_level          => severity_level,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      end_event               => end_event_d_2,
      fire                    => fire
    );
end architecture str;


------------------------------------------------------------------------------
-- ovl_win_unchange
------------------------------------------------------------------------------
library ieee, accellera_ovl_vlog;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use work.std_ovl_procs.all;
use work.std_ovl_components.all;

entity ovl_win_unchange is
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
end entity ovl_win_unchange;

architecture str of ovl_win_unchange is
  signal start_event_d_1 : std_logic;
  signal start_event_d_2 : std_logic;
  signal test_expr_d_1   : std_logic_vector(width - 1 downto 0);
  signal test_expr_d_2   : std_logic_vector(width - 1 downto 0);
  signal end_event_d_1   : std_logic;
  signal end_event_d_2   : std_logic;
begin
  start_event_d_1 <= start_event;
  start_event_d_2 <= start_event_d_1;
  test_expr_d_1   <= test_expr;
  test_expr_d_2   <= test_expr_d_1;
  end_event_d_1   <= end_event;
  end_event_d_2   <= end_event_d_1;

  u : entity accellera_ovl_vlog.ovl_win_unchange
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event_d_2,
      test_expr               => test_expr_d_2,
      end_event               => end_event_d_2,
      fire                    => fire
    );
end architecture str;

