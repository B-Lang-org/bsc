-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;

package std_ovl is

  -- subtypes for common generics
  subtype ovl_severity_level              is integer            range -1 to 3;
  subtype ovl_severity_level_natural      is ovl_severity_level range  0 to ovl_severity_level'high;
  subtype ovl_property_type               is integer            range -1 to 4;
  subtype ovl_property_type_natural       is ovl_property_type  range  0 to ovl_property_type'high;
  subtype ovl_coverage_level              is integer            range -1 to 15;
  subtype ovl_coverage_level_natural      is ovl_coverage_level range  0 to ovl_coverage_level'high;
  subtype ovl_active_edges                is integer            range -1 to 3;
  subtype ovl_active_edges_natural        is ovl_active_edges   range  0 to ovl_active_edges'high;
  subtype ovl_reset_polarity              is integer            range -1 to 1;
  subtype ovl_reset_polarity_natural      is ovl_reset_polarity range  0 to ovl_reset_polarity'high;
  subtype ovl_gating_type                 is integer            range -1 to 2;
  subtype ovl_gating_type_natural         is ovl_gating_type    range  0 to ovl_gating_type'high;

  -- subtypes for checker specific generics
  subtype ovl_necessary_condition         is integer            range  0 to 2;
  subtype ovl_action_on_new_start         is integer            range  0 to 2;
  subtype ovl_inactive                    is integer            range  0 to 2;
  subtype ovl_positive_2                  is integer            range  2 to integer'high;
  subtype ovl_chk_overlap                 is integer            range  0 to 1;
  
  -- subtypes for control constants
  subtype ovl_ctrl                        is integer            range  0 to 1;
  subtype ovl_msg_default_type            is string(1 to 50);
  
  -- user modifiable library control items
  type ovl_ctrl_record is record 
    -- generate statement controls
    xcheck_ctrl                 : ovl_ctrl;   
    implicit_xcheck_ctrl        : ovl_ctrl;   
    init_msg_ctrl               : ovl_ctrl;   
    init_count_ctrl             : ovl_ctrl;
    assert_ctrl                 : ovl_ctrl;   
    cover_ctrl                  : ovl_ctrl;   
    global_reset_ctrl           : ovl_ctrl;   
    finish_ctrl                 : ovl_ctrl;   
    gating_ctrl                 : ovl_ctrl;

    -- user configurable library constants                             
    max_report_error            : natural;
    max_report_cover_point      : natural;
    runtime_after_fatal         : string(1 to 10);

    -- default values for common generics 
    severity_level_default      : ovl_severity_level_natural;
    property_type_default       : ovl_property_type_natural;
    msg_default                 : ovl_msg_default_type;
    coverage_level_default      : ovl_coverage_level_natural;
    clock_edge_default          : ovl_active_edges_natural;
    reset_polarity_default      : ovl_reset_polarity_natural;
    gating_type_default         : ovl_gating_type_natural;
    
  end record ovl_ctrl_record;
  
  -- global signals
  signal ovl_global_reset_signal           : std_logic;
  signal ovl_end_of_simulation_signal      : std_logic := '0';
  
  -- global variable
  shared variable ovl_init_count           : natural := 0; 
 
  ------------------------------------------------------------------------------ 
  ------------------------------------------------------------------------------ 
  -- Hard-coded library constants                                             --
  -- NOTE:  These constants must not be changed by users. Users can configure --
  --        the library using the ovl_ctrl_record. Please see the OVL LRM for --
  --        details of how to do this.                                        --
  ------------------------------------------------------------------------------ 
  ------------------------------------------------------------------------------ 
  constant OVL_VERSION                     : string := "V2.8";

  -- This constant may be changed in future releases of the library or by EDA vendors. 
  constant OVL_FIRE_WIDTH                  : natural := 3;

  constant OVL_NOT_SET                     : integer := -1;
  
  -- generate statement control constants
  constant OVL_ON                          : ovl_ctrl := 1;
  constant OVL_OFF                         : ovl_ctrl := 0;
  
  -- fire bit selection constants
  constant OVL_FIRE_2STATE                 : integer := 0;
  constant OVL_FIRE_XCHECK                 : integer := 1;
  constant OVL_FIRE_COVER                  : integer := 2;
  
  -- severity level 
  constant OVL_SEVERITY_LEVEL_NOT_SET      : ovl_severity_level := OVL_NOT_SET; 
  constant OVL_FATAL                       : ovl_severity_level := 0; 
  constant OVL_ERROR                       : ovl_severity_level := 1; 
  constant OVL_WARNING                     : ovl_severity_level := 2; 
  constant OVL_INFO                        : ovl_severity_level := 3; 

  -- coverage levels
  constant OVL_COVERAGE_LEVEL_NOT_SET      : ovl_coverage_level := OVL_NOT_SET;
  constant OVL_COVER_NONE                  : ovl_coverage_level := 0;
  constant OVL_COVER_SANITY                : ovl_coverage_level := 1;
  constant OVL_COVER_BASIC                 : ovl_coverage_level := 2;
  constant OVL_COVER_CORNER                : ovl_coverage_level := 4;
  constant OVL_COVER_STATISTIC             : ovl_coverage_level := 8;
  constant OVL_COVER_ALL                   : ovl_coverage_level := 15;

  -- property type
  constant OVL_PROPERTY_TYPE_NOT_SET       : ovl_property_type := OVL_NOT_SET;
  constant OVL_ASSERT                      : ovl_property_type := 0;
  constant OVL_ASSUME                      : ovl_property_type := 1;
  constant OVL_IGNORE                      : ovl_property_type := 2;
  constant OVL_ASSERT_2STATE               : ovl_property_type := 3;
  constant OVL_ASSUME_2STATE               : ovl_property_type := 4;

  -- active edges
  constant OVL_ACTIVE_EDGES_NOT_SET        : ovl_active_edges := OVL_NOT_SET;   
  constant OVL_NOEDGE                      : ovl_active_edges := 0;   
  constant OVL_POSEDGE                     : ovl_active_edges := 1;   
  constant OVL_NEGEDGE                     : ovl_active_edges := 2;   
  constant OVL_ANYEDGE                     : ovl_active_edges := 3;   
  
  -- necessary condition
  constant OVL_TRIGGER_ON_MOST_PIPE        : ovl_necessary_condition := 0;
  constant OVL_TRIGGER_ON_FIRST_PIPE       : ovl_necessary_condition := 1;
  constant OVL_TRIGGER_ON_FIRST_NOPIPE     : ovl_necessary_condition := 2;
  
  -- action on new start
  constant OVL_IGNORE_NEW_START            : ovl_action_on_new_start := 0;
  constant OVL_RESET_ON_NEW_START          : ovl_action_on_new_start := 1;
  constant OVL_ERROR_ON_NEW_START          : ovl_action_on_new_start := 2;

  -- inactive levels
  constant OVL_ALL_ZEROS                   : ovl_inactive := 0;
  constant OVL_ALL_ONES                    : ovl_inactive := 1;
  constant OVL_ONE_COLD                    : ovl_inactive := 2;
  
  -- reset polarity
  constant OVL_RESET_POLARITY_NOT_SET      : ovl_reset_polarity := OVL_NOT_SET;
  constant OVL_ACTIVE_LOW                  : ovl_reset_polarity := 0;
  constant OVL_ACTIVE_HIGH                 : ovl_reset_polarity := 1;

  -- gating type
  constant OVL_GATING_TYPE_NOT_SET         : ovl_gating_type := OVL_NOT_SET;
  constant OVL_GATE_NONE                   : ovl_gating_type := 0;
  constant OVL_GATE_CLOCK                  : ovl_gating_type := 1;
  constant OVL_GATE_RESET                  : ovl_gating_type := 2;

  -- ovl_next check_overlapping values
  constant OVL_CHK_OVERLAP_OFF             : ovl_chk_overlap := 1;
  constant OVL_CHK_OVERLAP_ON              : ovl_chk_overlap := 0;
  
  -- checker xcheck type
  constant OVL_IMPLICIT_XCHECK             : boolean := false;
  constant OVL_EXPLICIT_XCHECK             : boolean := true;

  -- common default values
  constant OVL_SEVERITY_DEFAULT            : ovl_severity_level                      := OVL_ERROR;
  constant OVL_PROPERTY_DEFAULT            : ovl_property_type                       := OVL_ASSERT;
  constant OVL_MSG_NUL                     : string(10 to ovl_msg_default_type'high) := (others => NUL);
  constant OVL_MSG_DEFAULT                 : ovl_msg_default_type                    := "VIOLATION" & OVL_MSG_NUL;
  constant OVL_MSG_NOT_SET                 : string                                  := " ";
  constant OVL_COVER_DEFAULT               : ovl_coverage_level                      := OVL_COVER_BASIC;
  constant OVL_CLOCK_EDGE_DEFAULT          : ovl_active_edges                        := OVL_POSEDGE;
  constant OVL_RESET_POLARITY_DEFAULT      : ovl_reset_polarity                      := OVL_ACTIVE_LOW;
  constant OVL_GATING_TYPE_DEFAULT         : ovl_gating_type                         := OVL_GATE_CLOCK;

  -- checker specific default values
  constant OVL_NECESSARY_CONDITION_DEFAULT : ovl_necessary_condition                 := OVL_TRIGGER_ON_MOST_PIPE;
  constant OVL_ACTION_ON_NEW_START_DEFAULT : ovl_action_on_new_start                 := OVL_IGNORE_NEW_START;
  constant OVL_INACTIVE_DEFAULT            : ovl_inactive                            := OVL_ONE_COLD;

  -- default library configuration 
  constant OVL_CTRL_DEFAULTS               : ovl_ctrl_record                         := 
  (
    -- generate statement controls
    xcheck_ctrl                 => OVL_ON,                                  
    implicit_xcheck_ctrl        => OVL_ON,                                  
    init_msg_ctrl               => OVL_OFF,                                  
    init_count_ctrl             => OVL_OFF, 
    assert_ctrl                 => OVL_ON,                                  
    cover_ctrl                  => OVL_OFF,                                  
    global_reset_ctrl           => OVL_OFF,                                  
    finish_ctrl                 => OVL_ON,
    gating_ctrl                 => OVL_ON,                                  

    -- user configurable library constants                             
    max_report_error            => 15,
    max_report_cover_point      => 15,
    runtime_after_fatal         => "100 ns    ",
    
    -- default values for common generics 
    severity_level_default      => OVL_SEVERITY_DEFAULT,
    property_type_default       => OVL_PROPERTY_DEFAULT,
    msg_default                 => OVL_MSG_DEFAULT,
    coverage_level_default      => OVL_COVER_DEFAULT,
    clock_edge_default          => OVL_CLOCK_EDGE_DEFAULT,
    reset_polarity_default      => OVL_RESET_POLARITY_DEFAULT,
    gating_type_default         => OVL_GATING_TYPE_DEFAULT   
  );
  
end package std_ovl;
