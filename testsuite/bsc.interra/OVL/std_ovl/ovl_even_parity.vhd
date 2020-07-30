-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;

entity ovl_even_parity is
  generic (
    severity_level      : ovl_severity_level      := OVL_SEVERITY_LEVEL_NOT_SET; 
    width               : integer                 := 1; 
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
    test_expr           : in  std_logic_vector(width-1 downto 0);
    fire                : out std_logic_vector(OVL_FIRE_WIDTH-1 downto 0)
  );
end entity ovl_even_parity;

