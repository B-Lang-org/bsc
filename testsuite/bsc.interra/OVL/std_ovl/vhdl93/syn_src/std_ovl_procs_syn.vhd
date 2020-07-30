-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

library ieee;
use ieee.std_logic_1164.all;
use ieee.numeric_std.all;
use work.std_ovl.all;

package std_ovl_procs is

  ------------------------------------------------------------------------------
  -- Users must only use the ovl_set_msg and ovl_print_init_count_proc        --
  -- subprograms. All other subprograms are for internal use only.            -- 
  ------------------------------------------------------------------------------

  ------------------------------------------------------------------------------
  -- ovl_set_msg
  --
  -- This allows the default message string to be set for a 
  -- ovl_ctrl_record.msg_default constant.
  ------------------------------------------------------------------------------
  function ovl_set_msg (
    constant default             : in    string
  ) return string;
  
  ------------------------------------------------------------------------------
  -- ovl_print_init_count_proc
  --
  -- This is used to print a message stating the number of checkers that have
  -- been initialized.
  ------------------------------------------------------------------------------
  procedure ovl_print_init_count_proc (
    constant controls            : in    ovl_ctrl_record
  );

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------

  ------------------------------------------------------------------------------
  -- ovl_error_proc
  ------------------------------------------------------------------------------
  procedure ovl_error_proc (
    constant err_msg             : in    string; 
    constant severity_level      : in    ovl_severity_level;
    constant property_type       : in    ovl_property_type;
    constant assert_name         : in    string;
    constant msg                 : in    string;
    constant path                : in    string;
    constant controls            : in    ovl_ctrl_record;
    signal   fatal_sig           : out   std_logic;
    variable error_count         : inout natural
  );
                                
  ------------------------------------------------------------------------------
  -- ovl_init_msg_proc
  ------------------------------------------------------------------------------
  procedure ovl_init_msg_proc (
    constant severity_level      : in    ovl_severity_level;
    constant property_type       : in    ovl_property_type;
    constant assert_name         : in    string;            
    constant msg                 : in    string;
    constant path                : in    string;
    constant controls            : in    ovl_ctrl_record
  );

  ------------------------------------------------------------------------------
  -- ovl_cover_proc
  ------------------------------------------------------------------------------
  procedure ovl_cover_proc (
    constant cvr_msg             : in    string;
    constant assert_name         : in    string;         
    constant path                : in    string;
    constant controls            : in    ovl_ctrl_record;
    variable cover_count         : inout natural
  );

  ------------------------------------------------------------------------------
  -- ovl_finish_proc
  ------------------------------------------------------------------------------
  procedure ovl_finish_proc (
    constant assert_name         : in    string;  
    constant path                : in    string;  
    constant runtime_after_fatal : in    string;
    signal   fatal_sig           : in    std_logic
  ); 

  ------------------------------------------------------------------------------
  -- ovl_2state_is_on
  ------------------------------------------------------------------------------
  function ovl_2state_is_on (
    constant controls            : in    ovl_ctrl_record;
    constant property_type       : in    ovl_property_type
  ) return boolean;
  
  ------------------------------------------------------------------------------
  -- ovl_xcheck_is_on
  ------------------------------------------------------------------------------
  function ovl_xcheck_is_on (
    constant controls            : in    ovl_ctrl_record;
    constant property_type       : in    ovl_property_type;
    constant explicit_x_check    : in    boolean
  ) return boolean;
  
  ------------------------------------------------------------------------------
  -- ovl_get_ctrl_val
  ------------------------------------------------------------------------------
  function ovl_get_ctrl_val (
    constant instance_val        : in    integer;
    constant default_ctrl_val    : in    natural
  ) return natural;
  
  ------------------------------------------------------------------------------
  -- ovl_get_ctrl_val
  ------------------------------------------------------------------------------
  function ovl_get_ctrl_val (
    constant instance_val        : in    string;
    constant default_ctrl_val    : in    string
  ) return string;
  
  ------------------------------------------------------------------------------
  -- cover_item_set
  ------------------------------------------------------------------------------
  function cover_item_set (
    constant level               : in    ovl_coverage_level;
    constant item                : in    ovl_coverage_level
  ) return boolean;

  ------------------------------------------------------------------------------
  -- ovl_is_x
  ------------------------------------------------------------------------------
  function ovl_is_x (
    s                            : in    std_logic
  ) return boolean;
  
  ------------------------------------------------------------------------------
  -- ovl_is_x
  ------------------------------------------------------------------------------
  function ovl_is_x (
    s                            : in    std_logic_vector
  ) return boolean;
  
  ------------------------------------------------------------------------------
  -- or_reduce
  ------------------------------------------------------------------------------
  function or_reduce (
    v                            : in    std_logic_vector
  ) return std_logic;

  ------------------------------------------------------------------------------
  -- and_reduce
  ------------------------------------------------------------------------------
  function and_reduce (
    v                            : in    std_logic_vector
  ) return std_logic;

  ------------------------------------------------------------------------------
  -- xor_reduce
  ------------------------------------------------------------------------------
  function xor_reduce (
    v                            : in    std_logic_vector
  ) return std_logic;

  ------------------------------------------------------------------------------
  -- "sll"
  ------------------------------------------------------------------------------
  function "sll" (
    l                            : in    std_logic_vector;
    r                            : in    integer
  ) return std_logic_vector;

  ------------------------------------------------------------------------------
  -- "srl"
  ------------------------------------------------------------------------------
  function "srl" (
    l                            : in    std_logic_vector;
    r                            : in    integer
  ) return std_logic_vector;


  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  -- unsigned comparison functions                                            --
  -- Note: the width of l must be > 0.                                        --
  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  
  ------------------------------------------------------------------------------
  -- ">"
  ------------------------------------------------------------------------------
  function ">" ( 
    l                            : in    std_logic_vector; 
    r                            : in    natural
  ) return boolean;

  ------------------------------------------------------------------------------
  -- "<"
  ------------------------------------------------------------------------------
  function "<" ( 
    l                            : in    std_logic_vector; 
    r                            : in    natural
  ) return boolean;

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------

end package std_ovl_procs;


package body std_ovl_procs is 

  ------------------------------------------------------------------------------
  -- Users must only use the ovl_set_msg and ovl_print_init_count_proc        --
  -- subprograms. All other subprograms are for internal use only.            -- 
  ------------------------------------------------------------------------------

  ------------------------------------------------------------------------------
  -- ovl_set_msg
  --
  -- This allows the default message string to be set for a 
  -- ovl_ctrl_record.msg_default constant.
  ------------------------------------------------------------------------------
  function ovl_set_msg (
    constant default             : in    string
  ) return string is
    variable new_default : ovl_msg_default_type := (others => NUL);
  begin
     new_default(1 to default'high) := default;
     return new_default;
  end function ovl_set_msg;
  
  ------------------------------------------------------------------------------
  -- ovl_print_init_count_proc
  --
  -- This is used to print a message stating the number of checkers that have
  -- been initialized.
  ------------------------------------------------------------------------------
  procedure ovl_print_init_count_proc (
    constant controls            : in    ovl_ctrl_record
  ) is
  begin
  end procedure ovl_print_init_count_proc;

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------


  ------------------------------------------------------------------------------
  -- ovl_error_proc
  ------------------------------------------------------------------------------
  procedure ovl_error_proc (
    constant err_msg             : in    string;            
    constant severity_level      : in    ovl_severity_level;
    constant property_type       : in    ovl_property_type; 
    constant assert_name         : in    string;            
    constant msg                 : in    string;            
    constant path                : in    string;            
    constant controls            : in    ovl_ctrl_record; 
    signal   fatal_sig           : out   std_logic;   
    variable error_count         : inout natural
  ) is      
  begin
  end procedure ovl_error_proc;

  ------------------------------------------------------------------------------
  -- ovl_init_msg_proc
  ------------------------------------------------------------------------------
  procedure ovl_init_msg_proc (
    constant severity_level      : in    ovl_severity_level;
    constant property_type       : in    ovl_property_type;
    constant assert_name         : in    string;            
    constant msg                 : in    string;            
    constant path                : in    string;
    constant controls            : in    ovl_ctrl_record
  ) is
  begin
  end procedure ovl_init_msg_proc;      

  ------------------------------------------------------------------------------
  -- ovl_cover_proc
  ------------------------------------------------------------------------------
  procedure ovl_cover_proc (
    constant cvr_msg             : in    string;
    constant assert_name         : in    string;         
    constant path                : in    string;         
    constant controls            : in    ovl_ctrl_record;
    variable cover_count         : inout natural
  ) is
  begin
  end procedure ovl_cover_proc;

  ------------------------------------------------------------------------------
  -- ovl_finish_proc
  ------------------------------------------------------------------------------
  procedure ovl_finish_proc (
    constant assert_name         : in    string; 
    constant path                : in    string; 
    constant runtime_after_fatal : in    string;                                
    signal   fatal_sig           : in    std_logic
  ) is
  begin
  end procedure ovl_finish_proc;

  ------------------------------------------------------------------------------
  -- ovl_2state_is_on
  ------------------------------------------------------------------------------
  function ovl_2state_is_on (
    constant controls            : in    ovl_ctrl_record;
    constant property_type       : in    ovl_property_type
  ) return boolean is
    constant property_type_ctrl  : ovl_property_type_natural  := 
      ovl_get_ctrl_val(property_type, controls.property_type_default);  
  begin
    return (controls.assert_ctrl = OVL_ON) and 
           (property_type_ctrl  /= OVL_IGNORE);
  end function ovl_2state_is_on; 
  
  ------------------------------------------------------------------------------
  -- ovl_xcheck_is_on
  ------------------------------------------------------------------------------
  function ovl_xcheck_is_on (
    constant controls            : in    ovl_ctrl_record;
    constant property_type       : in    ovl_property_type;
    constant explicit_x_check    : in    boolean
  ) return boolean is
    constant property_type_ctrl  : ovl_property_type_natural  := 
      ovl_get_ctrl_val(property_type, controls.property_type_default);  
  begin
    return (controls.assert_ctrl           = OVL_ON)            and
           (property_type_ctrl            /= OVL_IGNORE)        and
           (property_type_ctrl            /= OVL_ASSERT_2STATE) and
           (property_type_ctrl            /= OVL_ASSUME_2STATE) and
           (controls.xcheck_ctrl           = OVL_ON)            and
           ((controls.implicit_xcheck_ctrl = OVL_ON) or explicit_x_check);
  end function ovl_xcheck_is_on; 
  
  ------------------------------------------------------------------------------
  -- ovl_get_ctrl_val
  ------------------------------------------------------------------------------
  function ovl_get_ctrl_val (
    constant instance_val        : in    integer;
    constant default_ctrl_val    : in    natural
  ) return natural is
  begin
    if (instance_val = OVL_NOT_SET) then
      return default_ctrl_val;
    else
      return instance_val;
    end if;
  end function ovl_get_ctrl_val;
 
  ------------------------------------------------------------------------------
  -- ovl_get_ctrl_val
  ------------------------------------------------------------------------------
  function ovl_get_ctrl_val (
    constant instance_val        : in    string;
    constant default_ctrl_val    : in    string
  ) return string is
    variable msg_default_width : integer := ovl_msg_default_type'high;
  begin
    if (instance_val = OVL_MSG_NOT_SET) then
      -- get width of msg_default value
      for i in 1 to ovl_msg_default_type'high loop
        if (default_ctrl_val(i) = NUL) then
          msg_default_width := i - 1;
          exit;
        end if;
      end loop;
      
      return default_ctrl_val(1 to msg_default_width);
    else
      return instance_val;
    end if;
  end function ovl_get_ctrl_val;
 
  ------------------------------------------------------------------------------
  -- cover_item_set
  -- determines if a bit in the level integer is set or not. 
  ------------------------------------------------------------------------------
  function cover_item_set (
    constant level               : in    ovl_coverage_level;
    constant item                : in    ovl_coverage_level
  ) return boolean is
  begin
    return ((level mod (item * 2)) >= item);
  end function cover_item_set;

  ------------------------------------------------------------------------------
  -- ovl_is_x
  ------------------------------------------------------------------------------
  function ovl_is_x (
    s                            : in    std_logic
  ) return boolean is
  begin
    return false;
  end function ovl_is_x;

  ------------------------------------------------------------------------------
  -- ovl_is_x
  ------------------------------------------------------------------------------
  function ovl_is_x (
    s                            : in    std_logic_vector
  ) return boolean is
  begin
    return false;
  end function ovl_is_x;
  
  ------------------------------------------------------------------------------
  -- or_reduce
  ------------------------------------------------------------------------------
  function or_reduce (
    v                            : in    std_logic_vector
  ) return std_logic is
    variable result : std_logic;
  begin
    for i in v'range loop
      if i = v'left then
        result := v(i);
      else
        result := result or v(i);
      end if;
      exit when result = '1';
    end loop;
    return result;
  end function or_reduce;

  ------------------------------------------------------------------------------
  -- and_reduce
  ------------------------------------------------------------------------------
  function and_reduce (
    v                            : in    std_logic_vector
  ) return std_logic is
    variable result : std_logic;
  begin
    for i in v'range loop
      if i = v'left then
        result := v(i);
      else
        result := result and v(i);
      end if;
      exit when result = '0';
    end loop;
    return result;
  end function and_reduce;
  
  ------------------------------------------------------------------------------
  -- xor_reduce
  ------------------------------------------------------------------------------
  function xor_reduce (
    v                            : in    std_logic_vector
  ) return std_logic is
    variable result : std_logic;
  begin
    for i in v'range loop
      if i = v'left then
        result := v(i);
      else
        result := result xor v(i);
      end if;
    end loop;
    return result;
  end function xor_reduce;

  ------------------------------------------------------------------------------
  -- "sll"
  ------------------------------------------------------------------------------
  function "sll" (
    l                            : in    std_logic_vector;
    r                            : in    integer
  ) return std_logic_vector is
  begin
    return to_stdlogicvector(to_bitvector(l) sll r);
  end function "sll";

  ------------------------------------------------------------------------------
  -- "srl"
  ------------------------------------------------------------------------------
  function "srl" (
    l                            : in    std_logic_vector;
    r                            : in    integer
  ) return std_logic_vector is
  begin
    return to_stdlogicvector(to_bitvector(l) srl r);
  end function "srl";

  
  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  -- unsigned comparison functions                                            --
  -- Note: the width of l must be > 0.                                        --
  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------

  ------------------------------------------------------------------------------
  -- ">"
  ------------------------------------------------------------------------------
  function ">" ( 
    l                            : in    std_logic_vector; 
    r                            : in    natural
  ) return boolean is
  begin
    return unsigned(l) > r;
  end function ">";
  
  ------------------------------------------------------------------------------
  -- "<"
  ------------------------------------------------------------------------------
  function "<" ( 
    l                            : in    std_logic_vector; 
    r                            : in    natural
  ) return boolean is
  begin
    return unsigned(l) < r;
  end function "<";

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  
end package body std_ovl_procs;
