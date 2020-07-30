-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

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

end package std_ovl_components;
