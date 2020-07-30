-- Accellera Standard V2.8.1 Open Verification Library (OVL).
-- Accellera Copyright (c) 2012-2014. All rights reserved.

-- NOTE : This file is not suitable for use with synthesis tools, use 
--        std_ovl_procs_syn.vhd instead.

library ieee;
use ieee.std_logic_1164.all;
use work.std_ovl.all;
use std.textio.all;

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

  ------------------------------------------------------------------------------
  -- "logb2" - function to calculate the log base2 of the natural number
  ------------------------------------------------------------------------------
  function logb2 (a: natural) return natural;


  ------------------------------------------------------------------------------
  -- "to_integer" - function to convert std_logic_vector to integer
  ------------------------------------------------------------------------------
  function to_integer (OP: std_logic_vector) return integer;


  ------------------------------------------------------------------------------
  -- "check_condition_integer" - function to return specified integer value if exprerssion is true or false.
  ------------------------------------------------------------------------------
  function check_condition_integer (OP: BOOLEAN ; true_condition : integer ; false_condition : integer ) return integer;

  ------------------------------------------------------------------------------
  -- "ovl_action_on_new_start_cmp" - function to return '1' if both the inputs are same else '0'.
  ------------------------------------------------------------------------------
  function ovl_action_on_new_start_cmp (OP1: ovl_action_on_new_start; OP2: ovl_action_on_new_start) return std_logic;

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  type err_array is array (ovl_severity_level_natural) of string (1 to 16);
 
  constant err_typ : err_array := (OVL_FATAL   => "       OVL_FATAL", 
                                   OVL_ERROR   => "       OVL_ERROR", 
                                   OVL_WARNING => "     OVL_WARNING", 
                                   OVL_INFO    => "        OVL_INFO"); 
 
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
    constant default        : in    string
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
    variable ln : line;
  begin
    if ((controls.init_msg_ctrl = OVL_ON) and (controls.init_count_ctrl = OVL_ON)) then
      writeline(output, ln);
      write(ln, "OVL_METRICS: " & integer'image(ovl_init_count) & " OVL assertions initialized");
      writeline(output, ln);
      writeline(output, ln);
    end if;
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
    variable ln : line;
    constant severity_level_ctrl : ovl_severity_level_natural := 
      ovl_get_ctrl_val(severity_level, controls.severity_level_default);
    constant property_type_ctrl  : ovl_property_type_natural  := 
      ovl_get_ctrl_val(property_type, controls.property_type_default);
    constant msg_ctrl            : string                     := 
      ovl_get_ctrl_val(msg, controls.msg_default);
  begin
    error_count := error_count + 1;    

    if (error_count <= controls.max_report_error) then
      case (property_type_ctrl) is       
        when OVL_ASSERT | OVL_ASSUME | OVL_ASSERT_2STATE | OVL_ASSUME_2STATE => 
          write(ln, err_typ(severity_level_ctrl) & " : "
                    & assert_name & " : "
                    & msg_ctrl & " : "
                    & err_msg
                    & " : severity " & ovl_severity_level'image(severity_level_ctrl)
                    & " : time " & time'image(now)
                    & " " & path);
          writeline(output, ln);
        when OVL_IGNORE => null;
      end case;          
    end if;   

    if ((severity_level_ctrl = OVL_FATAL) and (controls.finish_ctrl = OVL_ON)) then
      fatal_sig <= '1';
    end if;
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
    variable ln : line;
    constant severity_level_ctrl : ovl_severity_level_natural := 
      ovl_get_ctrl_val(severity_level, controls.severity_level_default);
    constant property_type_ctrl  : ovl_property_type_natural  := 
      ovl_get_ctrl_val(property_type, controls.property_type_default);
    constant msg_ctrl            : string                     := 
      ovl_get_ctrl_val(msg, controls.msg_default);
  begin
    if (controls.init_count_ctrl = OVL_ON) then
      ovl_init_count := ovl_init_count + 1;
    else
      case (property_type_ctrl) is       
        when OVL_ASSERT | OVL_ASSUME | OVL_ASSERT_2STATE | OVL_ASSUME_2STATE => 
          write(ln, "OVL_NOTE: " & OVL_VERSION & ": " 
                    & assert_name 
                    & " initialized @ " & path 
                    & " Severity: " & ovl_severity_level'image(severity_level_ctrl)
                    & ", Message: " & msg_ctrl);
          writeline(output, ln);
        when OVL_IGNORE => NULL;
      end case; 
    end if;         
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
    variable ln : line;
  begin
    cover_count := cover_count + 1;

    if (cover_count <= controls.max_report_cover_point) then
       write(ln, "OVL_COVER_POINT : "
              & assert_name & " : "
              & cvr_msg & " : "
              & "time " & time'image(now)
              & " " & path);
      writeline(output, ln);  
    end if;
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
    variable ln : line;
    variable runtime_after_fatal_time : time;
  begin
    if (fatal_sig = '1') then
      -- convert string to time
      write(ln, runtime_after_fatal);
      read(ln, runtime_after_fatal_time);

      wait for runtime_after_fatal_time;
      report "       OVL : Simulation stopped due to a fatal error : " & assert_name & " : " & "time " &
              time'image(now) & " " & path severity failure;
    end if;
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
    return is_x(s);
  end function ovl_is_x;

  ------------------------------------------------------------------------------
  -- ovl_is_x
  ------------------------------------------------------------------------------
  function ovl_is_x (
    s                            : in    std_logic_vector
  ) return boolean is
  begin
    return is_x(s);
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
  -- private functions used by "<" and ">" functions                          --
  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------
  
  ------------------------------------------------------------------------------
  -- unsigned_num_bits
  ------------------------------------------------------------------------------
  function unsigned_num_bits (arg: natural) return natural is
    variable nbits: natural;
    variable n: natural;
  begin
    n := arg;
    nbits := 1;
    while n > 1 loop
      nbits := nbits+1;
      n := n / 2;
    end loop;
    return nbits;
  end unsigned_num_bits;

  ------------------------------------------------------------------------------
  -- to_unsigned
  ------------------------------------------------------------------------------
  function to_unsigned (arg, size: natural) return std_logic_vector is
    variable result: std_logic_vector(size-1 downto 0);
    variable i_val: natural := arg;
  begin
    for i in 0 to result'left loop
      if (i_val mod 2) = 0 then
        result(i) := '0';
      else result(i) := '1';
      end if;
      i_val := i_val/2;
    end loop;
    return result;
  end to_unsigned;

  ------------------------------------------------------------------------------
  ------------------------------------------------------------------------------


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
    if is_x(l) then return false; end if;
    if unsigned_num_bits(r) > l'length then return false; end if;
    return not (l <= to_unsigned(r, l'length));
  end function ">";
  
  ------------------------------------------------------------------------------
  -- "<"
  ------------------------------------------------------------------------------
  function "<" ( 
    l                            : in    std_logic_vector; 
    r                            : in    natural
  ) return boolean is
  begin
    if is_x(l) then return false; end if;
    if unsigned_num_bits(r) > l'length then return 0 < r; end if;
    return (l < to_unsigned(r, l'length));
  end function "<";

  ------------------------------------------------------------------------------
  -- "logb2" - function to calculate the log base2 of the natural number
             -- a - Input Natrual Number 
             --     Output is logbase2(a)       
  ------------------------------------------------------------------------------
 
  function logb2 (a: NATURAL) return NATURAL IS
        variable aggregate : NATURAL := a;
        variable return_val : NATURAL := 0;
    begin
        compute_clogb2: 
        for i in a downto 0 loop
            IF aggregate > 0 then
                return_val := return_val + 1;
            end IF;
            aggregate := aggregate / 2; 
        end loop;
 
        return return_val;
    end logb2;

    -----------------------------------------------------------------------
    -- "to_integer" - function to convert std_logic_vector to integer
    -- Convert passed std_logic_vector into integer.
    -- generate warning message if:
    --  array contains anything other than 0 or 1.
    ------------------------------------------------------------------------
    function to_integer (OP: STD_LOGIC_VECTOR)
      return inTEGER is
      variable result : inTEGER := 0;
      variable tmp_op : STD_LOGIC_VECTOR (OP'range) := OP;
    begin
      if not (Is_X(OP)) then
        for i in OP'range loop
          if OP(i) = '1' then
            result := result + 2**i;
          end if;
        end loop; 
        return result;
      -- OP contains anything other than 0 or 1
      else
      --  assert FALSE
      --    report "Illegal value detected in the conversion of to_integer"
      --    severity WARNinG;
            return 0;
      end if;
    end to_integer;

  ------------------------------------------------------------------------------
  -- "check_condition_integer" - function to return specified integer value if 
  --                             exprerssion is true or false.
  --                     OP             : Input Boolean Expression
  --                     true_condition : Input integer which will be returned if Boolean Expression is true
  --                     false_condition: Input integer which will be returned if Boolean Expression is false
  ------------------------------------------------------------------------------
  function check_condition_integer (OP: BOOLEAN ; true_condition : integer ; false_condition : integer ) return integer is
    begin
      if (OP) then
        return true_condition;
      else
        return false_condition;
      end if;
    end check_condition_integer;
 
 ------------------------------------------------------------------------------
  -- "ovl_action_on_new_start_cmp" - function to return '1' when both OP1 and OP2 are same else '0' 
  --                     OP1            : Input ovl_action_on_new_start
  --                     OP2            : Input ovl_action_on_new_start
  ------------------------------------------------------------------------------
  function ovl_action_on_new_start_cmp (OP1: ovl_action_on_new_start ; OP2: ovl_action_on_new_start) return std_logic is
    begin
      if (OP1 = OP2) then
        return '1';
      else
        return '0';
      end if;
    end ovl_action_on_new_start_cmp;

end package body std_ovl_procs;
