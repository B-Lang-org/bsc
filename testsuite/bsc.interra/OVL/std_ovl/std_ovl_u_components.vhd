-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved

library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

package std_ovl_u_components is

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
      clock               : in  std_ulogic;
      reset               : in  std_ulogic;
      enable              : in  std_ulogic;
      test_expr           : in  std_ulogic;
      fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
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
      clock               : in  std_ulogic;
      reset               : in  std_ulogic;
      enable              : in  std_ulogic;
      test_expr           : in  std_ulogic;
      fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
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
      clock               : in  std_ulogic;
      reset               : in  std_ulogic;
      enable              : in  std_ulogic;
      start_event         : in  std_ulogic;
      test_expr           : in  std_ulogic;
      fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
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
      clock               : in  std_ulogic;
      reset               : in  std_ulogic;
      enable              : in  std_ulogic;
      event_sequence      : in  std_ulogic_vector(num_cks        - 1 downto 0);
      fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_cycle_sequence;

  ------------------------------------------------------------------------------
  -- ovl_zero_one_hot
  ------------------------------------------------------------------------------
  component ovl_zero_one_hot
    generic (
      severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width          : positive           := 32;
      property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg            : string             := OVL_MSG_NOT_SET;
      coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock          : in  std_ulogic;
      reset          : in  std_ulogic;
      enable         : in  std_ulogic;
      test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
      fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_zero_one_hot;

  ------------------------------------------------------------------------------
  -- ovl_range
  ------------------------------------------------------------------------------
  component ovl_range
    generic (
      severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width          : positive           := 1;
      min            : natural            := 0;
      max            : natural            := 1;
      property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg            : string             := OVL_MSG_NOT_SET;
      coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock          : in  std_ulogic;
      reset          : in  std_ulogic;
      enable         : in  std_ulogic;
      test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
      fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_range;

  ------------------------------------------------------------------------------
  -- ovl_one_hot
  ------------------------------------------------------------------------------
  component ovl_one_hot
    generic (
      severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width          : positive           := 32;
      property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg            : string             := OVL_MSG_NOT_SET;
      coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock          : in  std_ulogic;
      reset          : in  std_ulogic;
      enable         : in  std_ulogic;
      test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
      fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_one_hot;

  ------------------------------------------------------------------------------
  -- ovl_never_unknown
  ------------------------------------------------------------------------------
  component ovl_never_unknown
    generic (
      severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width          : positive           := 1;
      property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg            : string             := OVL_MSG_NOT_SET;
      coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock          : in  std_ulogic;
      reset          : in  std_ulogic;
      enable         : in  std_ulogic;
      qualifier      : in  std_ulogic;
      test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
      fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_never_unknown;

  ------------------------------------------------------------------------------
  -- ovl_never_unknown_async
  ------------------------------------------------------------------------------
  component ovl_never_unknown_async
    generic (
      severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      width          : positive           := 1;
      property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg            : string             := OVL_MSG_NOT_SET;
      coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      reset          : in  std_ulogic;
      enable         : in  std_ulogic;
      test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
      fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_never_unknown_async;

  ------------------------------------------------------------------------------
  -- ovl_implication
  ------------------------------------------------------------------------------
  component ovl_implication
    generic (
      severity_level  : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
      property_type   : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
      msg             : string             := OVL_MSG_NOT_SET;
      coverage_level  : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
      clock_edge      : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
      reset_polarity  : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
      gating_type     : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
      controls        : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
    );
    port (
      clock           : in  std_ulogic;
      reset           : in  std_ulogic;
      enable          : in  std_ulogic;
      antecedent_expr : in  std_ulogic;
      consequent_expr : in  std_ulogic;
      fire            : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
    );
  end component ovl_implication;

end package std_ovl_u_components;


--------------------------------------------------------------------------------
-- ovl_always
--------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;
use accellera_ovl_vhdl.std_ovl_components.all;

entity ovl_always is
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
    clock               : in  std_ulogic;
    reset               : in  std_ulogic;
    enable              : in  std_ulogic;
    test_expr           : in  std_ulogic;
    fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_always;

architecture str of ovl_always is
begin
  u : entity accellera_ovl_vhdl.ovl_always
    generic map (
      severity_level          => severity_level,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr,
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_never
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_never is
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
    clock               : in  std_ulogic;
    reset               : in  std_ulogic;
    enable              : in  std_ulogic;
    test_expr           : in  std_ulogic;
    fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_never;

architecture str of ovl_never is
begin
  u : entity accellera_ovl_vhdl.ovl_never
    generic map (
      severity_level          => severity_level,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => test_expr,
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_next
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_next is
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
    clock               : in  std_ulogic;
    reset               : in  std_ulogic;
    enable              : in  std_ulogic;
    start_event         : in  std_ulogic;
    test_expr           : in  std_ulogic;
    fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_next;

architecture str of ovl_next is
begin
  u : entity accellera_ovl_vhdl.ovl_next
    generic map (
      severity_level          => severity_level,
      num_cks                 => num_cks,
      check_overlapping       => check_overlapping,
      check_missing_start     => check_missing_start,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      start_event             => start_event,
      test_expr               => test_expr,
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_cycle_sequence
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_cycle_sequence is
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
    clock               : in  std_ulogic;
    reset               : in  std_ulogic;
    enable              : in  std_ulogic;
    event_sequence      : in  std_ulogic_vector(num_cks        - 1 downto 0);
    fire                : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_cycle_sequence;

architecture str of ovl_cycle_sequence is
begin
  u : entity accellera_ovl_vhdl.ovl_cycle_sequence
    generic map (
      severity_level          => severity_level,
      num_cks                 => num_cks,
      necessary_condition     => necessary_condition,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      event_sequence          => std_logic_vector(event_sequence),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_zero_one_hot
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_zero_one_hot is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    width          : positive           := 32;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    clock          : in  std_ulogic;
    reset          : in  std_ulogic;
    enable         : in  std_ulogic;
    test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
    fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_zero_one_hot;

architecture str of ovl_zero_one_hot is
begin
  u : entity accellera_ovl_vhdl.ovl_zero_one_hot
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => std_logic_vector(test_expr),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_range
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_range is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    width          : positive           := 1;
    min            : natural            := 0;
    max            : natural            := 1;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    clock          : in  std_ulogic;
    reset          : in  std_ulogic;
    enable         : in  std_ulogic;
    test_expr      : in  std_ulogic_vector(width            - 1 downto 0);
    fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_range;

architecture str of ovl_range is
begin
  u : entity accellera_ovl_vhdl.ovl_range
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
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => std_logic_vector(test_expr),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_one_hot
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_one_hot is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    width          : positive           := 32;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    clock          : in  std_ulogic;
    reset          : in  std_ulogic;
    enable         : in  std_ulogic;
    test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
    fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_one_hot;

architecture str of ovl_one_hot is
begin
  u : entity accellera_ovl_vhdl.ovl_one_hot
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      test_expr               => std_logic_vector(test_expr),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_never_unknown
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_never_unknown is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    width          : positive           := 1;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    clock          : in  std_ulogic;
    reset          : in  std_ulogic;
    enable         : in  std_ulogic;
    qualifier      : in  std_ulogic;
    test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
    fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_never_unknown;

architecture str of ovl_never_unknown is
begin
  u : entity accellera_ovl_vhdl.ovl_never_unknown
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      qualifier               => qualifier,
      test_expr               => std_logic_vector(test_expr),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_never_unknown_async
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_never_unknown_async is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    width          : positive           := 1;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    reset          : in  std_ulogic;
    enable         : in  std_ulogic;
    test_expr      : in  std_ulogic_vector(width          - 1 downto 0);
    fire           : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_never_unknown_async;

architecture str of ovl_never_unknown_async is
begin
  u : entity accellera_ovl_vhdl.ovl_never_unknown_async
    generic map (
      severity_level          => severity_level,
      width                   => width,
      property_type           => property_type,
      msg                     => msg,
      coverage_level          => coverage_level,
      clock_edge              => clock_edge,
      reset_polarity          => reset_polarity,
      gating_type             => gating_type,
      controls                => controls
    )
    port map (
      reset                   => reset,
      enable                  => enable,
      test_expr               => std_logic_vector(test_expr),
      std_ulogic_vector(fire) => fire
    );
end architecture str;


---------------------------------------------------------------------------------
-- ovl_implication
---------------------------------------------------------------------------------
library ieee, accellera_ovl_vhdl;
use ieee.std_logic_1164.all;
use accellera_ovl_vhdl.std_ovl.all;

entity ovl_implication is
  generic (
    severity_level : ovl_severity_level := OVL_SEVERITY_LEVEL_NOT_SET;
    property_type  : ovl_property_type  := OVL_PROPERTY_TYPE_NOT_SET;
    msg            : string             := OVL_MSG_NOT_SET;
    coverage_level : ovl_coverage_level := OVL_COVERAGE_LEVEL_NOT_SET;
    clock_edge     : ovl_active_edges   := OVL_ACTIVE_EDGES_NOT_SET;
    reset_polarity : ovl_reset_polarity := OVL_RESET_POLARITY_NOT_SET;
    gating_type    : ovl_gating_type    := OVL_GATING_TYPE_NOT_SET;
    controls       : ovl_ctrl_record    := OVL_CTRL_DEFAULTS
  );
  port (
    clock           : in  std_ulogic;
    reset           : in  std_ulogic;
    enable          : in  std_ulogic;
    antecedent_expr : in  std_ulogic;
    consequent_expr : in  std_ulogic;
    fire            : out std_ulogic_vector(OVL_FIRE_WIDTH - 1 downto 0)
  );
end entity ovl_implication;

architecture str of ovl_implication is
begin
  u : entity accellera_ovl_vhdl.ovl_implication
    generic map (
      severity_level         => severity_level,
      property_type          => property_type,
      msg                    => msg,
      coverage_level         => coverage_level,
      clock_edge             => clock_edge,
      reset_polarity         => reset_polarity,
      gating_type            => gating_type,
      controls               => controls
    )
    port map (
      clock                   => clock,
      reset                   => reset,
      enable                  => enable,
      antecedent_expr         => antecedent_expr,
      consequent_expr         => consequent_expr,
      std_ulogic_vector(fire) => fire
    );
end architecture str;

