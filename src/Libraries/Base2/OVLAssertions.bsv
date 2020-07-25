////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

package OVLAssertions;

`include "std_ovl_defines.h"

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

typedef enum {OVL_FATAL = `OVL_FATAL,
	      OVL_ERROR = `OVL_ERROR,
	      OVL_WARNING = `OVL_WARNING,
	      OVL_INFO = `OVL_INFO,
	      DEFAULT, ILLEGAL} OVLSeverityLevel deriving(Bits, Eq);

typedef enum {OVL_ASSERT = `OVL_ASSERT,
	      OVL_ASSUME = `OVL_ASSUME,
	      OVL_IGNORE = `OVL_IGNORE,
	      DEFAULT, ILLEGAL} OVLPropertyType deriving(Bits, Eq);

typedef enum {OVL_COVER_NONE = `OVL_COVER_NONE,
	      OVL_COVER_ALL = `OVL_COVER_ALL,
	      OVL_COVER_SANITY = `OVL_COVER_SANITY,
	      OVL_COVER_BASIC = `OVL_COVER_BASIC,
	      OVL_COVER_CORNER = `OVL_COVER_CORNER,
	      OVL_COVER_STATISTIC = `OVL_COVER_STATISTIC,
	      DEFAULT, ILLEGAL} OVLCoverageLevel deriving(Bits, Eq);

////////////////////////////////////////////////////////////////////////////////

////////////////////////////////////////////////////////////////////////////////

typedef enum {OVL_IGNORE_NEW_START   = `OVL_IGNORE_NEW_START,
	      OVL_RESET_ON_NEW_START = `OVL_RESET_ON_NEW_START,
	      OVL_ERROR_ON_NEW_START = `OVL_ERROR_ON_NEW_START,
	      DEFAULT, ILLEGAL} OVLActionOnNewStart deriving(Bits, Eq);

typedef enum {OVL_NOEDGE  = `OVL_NOEDGE,
	      OVL_POSEDGE = `OVL_POSEDGE,
	      OVL_NEGEDGE = `OVL_NEGEDGE,
	      OVL_ANYEDGE = `OVL_ANYEDGE,
	      DEFAULT, ILLEGAL} OVLEdgeType deriving(Bits, Eq);

typedef enum {OVL_TRIGGER_ON_MOST_PIPE    = `OVL_TRIGGER_ON_MOST_PIPE,
	      OVL_TRIGGER_ON_FIRST_PIPE   = `OVL_TRIGGER_ON_FIRST_PIPE,
	      OVL_TRIGGER_ON_FIRST_NOPIPE = `OVL_TRIGGER_ON_FIRST_NOPIPE,
	      DEFAULT, ILLEGAL} OVLNecessaryCondition deriving(Bits, Eq);

typedef enum {OVL_ALL_ZEROS = `OVL_ALL_ZEROS,
	      OVL_ALL_ONES  = `OVL_ALL_ONES,
	      OVL_ONE_COLD  = `OVL_ONE_COLD,
	      DEFAULT, ILLEGAL} OVLInactive deriving(Bits, Eq);

typedef struct {
		OVLSeverityLevel      severity_level;
		OVLPropertyType       property_type;
		String                msg;
		OVLCoverageLevel      coverage_level;
		OVLActionOnNewStart   action_on_new_start;
		OVLEdgeType           edge_type;
		OVLNecessaryCondition necessary_condition;
		OVLInactive           inactive;
		Int#(32)              num_cks;
		Int#(32)              min_cks;
		Int#(32)              max_cks;
		Int#(32)              min_ack_cycle;
		Int#(32)              max_ack_cycle;
		Int#(32)              max_ack_length;
		Int#(32)              req_drop;
		Int#(32)              deassert_count;
		Int#(32)              depth;
		a                     value;
		a                     min;
		a                     max;
		Bool                  check_overlapping;
		Bool                  check_missing_start;
		Bool                  simultaneous_push_pop;
   		} OVLDefaults#(type a);

typedef struct {
		Maybe#(OVLSeverityLevel)      severity_level;
		Maybe#(OVLPropertyType)       property_type;
		Maybe#(String)                msg;
		Maybe#(OVLCoverageLevel)      coverage_level;
		Maybe#(OVLActionOnNewStart)   action_on_new_start;
		Maybe#(OVLEdgeType)           edge_type;
		Maybe#(OVLNecessaryCondition) necessary_condition;
		Maybe#(OVLInactive)           inactive;
		Maybe#(Int#(32))              num_cks;	
		Maybe#(Int#(32))              min_cks;
		Maybe#(Int#(32))              max_cks;
		Maybe#(Int#(32))              min_ack_cycle;
		Maybe#(Int#(32))              max_ack_cycle;
		Maybe#(Int#(32))              max_ack_length;
		Maybe#(Int#(32))              req_drop;
		Maybe#(Int#(32))              deassert_count;
		Maybe#(Int#(32))              depth;
		Maybe#(a)                     value;
		Maybe#(a)                     min;
		Maybe#(a)                     max;
		Maybe#(Bool)                  check_overlapping;
		Maybe#(Bool)                  check_missing_start;
		Maybe#(Bool)                  simultaneous_push_pop;
		} OVLDefaultsTemplate#(type a);

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

String default_msg = "_DEFAULT";
Int#(32) default_num = -1000;

function OVLDefaults#(a) mkOVLDefaults()
   provisos(Bounded#(a));

   return OVLDefaults {severity_level:      DEFAULT,
		       property_type:       DEFAULT,
		       msg:                 default_msg,
		       coverage_level:      DEFAULT,
		       action_on_new_start: DEFAULT,
		       edge_type:           DEFAULT,
		       necessary_condition: DEFAULT,
		       inactive:            DEFAULT,
		       num_cks:             default_num,
		       min_cks:             default_num,
		       max_cks:             default_num,
			   min_ack_cycle:       default_num,
			   max_ack_cycle:       default_num,
			   max_ack_length:      default_num,
			   req_drop:            default_num,
			   deassert_count:      default_num,
			   depth:               default_num,
		       value:               minBound,
		       min:                 minBound,
		       max:                 maxBound,
		       check_overlapping:   True,
		       check_missing_start: False,
			   simultaneous_push_pop: True
		       };
endfunction

function OVLDefaultsTemplate#(a) mkOVLDefaultsTemplate();

   return OVLDefaultsTemplate {severity_level:        Invalid,
			       property_type:         Invalid,
			       msg:                   Invalid,
			       coverage_level:        Invalid,
			       action_on_new_start:   Invalid,
			       edge_type:             Invalid,
			       necessary_condition:   Invalid,
			       inactive:              Invalid,
			       num_cks:               Invalid,
			       min_cks:               Invalid,
			       max_cks:               Invalid,
			       min_ack_cycle:         Invalid,
			       max_ack_cycle:         Invalid,
			       max_ack_length:        Invalid,
			       req_drop:              Invalid,
			       deassert_count:        Invalid,
			       depth:                 Invalid,
			       value:                 Invalid,
			       min:                   Invalid,
			       max:                   Invalid,
			       check_overlapping:     Invalid,
			       check_missing_start:   Invalid,
			       simultaneous_push_pop: Invalid
		       };
endfunction

////////////////////////////////////////////////////////////////////////////////
///
////////////////////////////////////////////////////////////////////////////////

function OVLDefaults#(a) updateOVLDefaults (OVLDefaults#(a) defaults,
					    OVLDefaultsTemplate#(a) template,
					    String name)
   provisos(Bounded#(a), Eq#(a));

   defaults = updateOVLSeverityLevel(defaults, template, name);
   defaults = updateOVLPropertyType(defaults, template, name);
   defaults = updateOVLMsg(defaults, template, name);
   defaults = updateOVLCoverageLevel(defaults, template, name);
   defaults = updateOVLActionOnNewStart(defaults, template, name);
   defaults = updateOVLEdgeType(defaults, template, name);
   defaults = updateOVLNecessaryCondition(defaults, template, name);
   defaults = updateOVLInactive(defaults, template, name);
   defaults = updateOVLNumCks(defaults, template, name);
   defaults = updateOVLMinCks(defaults, template, name);
   defaults = updateOVLMaxCks(defaults, template, name);
   defaults = updateOVLMinAckCycle(defaults, template, name);
   defaults = updateOVLMaxAckCycle(defaults, template, name);
   defaults = updateOVLMaxAckLength(defaults, template, name);
   defaults = updateOVLReqDrop(defaults, template, name);
   defaults = updateOVLDeassertCount(defaults, template, name);
   defaults = updateOVLDepth(defaults, template, name);
   defaults = updateOVLValue(defaults, template, name);
   defaults = updateOVLMin(defaults, template, name);
   defaults = updateOVLMax(defaults, template, name);
   defaults = updateOVLCheckOverlapping(defaults, template, name);
   defaults = updateOVLCheckMissingStart(defaults, template, name);
   defaults = updateOVLSimultaneousPushPop(defaults, template, name);

   return defaults;

endfunction

function OVLDefaults#(a) updateOVLSeverityLevel (OVLDefaults#(a) defaults,
						 OVLDefaultsTemplate#(a) template,
						 String name);
   let defaults_mod = defaults;
   if (isValid(template.severity_level))
      defaults_mod.severity_level = validValue(template.severity_level);

   let value = ((defaults.severity_level == DEFAULT) ?
		defaults_mod :
      ((template.severity_level == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"severity_level\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction


function OVLDefaults#(a) updateOVLPropertyType (OVLDefaults#(a) defaults,
						OVLDefaultsTemplate#(a) template,
						String name);
   let defaults_mod = defaults;
   if (isValid(template.property_type))
      defaults_mod.property_type = validValue(template.property_type);

   let value = ((defaults.property_type == DEFAULT) ?
		defaults_mod :
      ((template.property_type == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"property_type\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMsg (OVLDefaults#(a) defaults,
				       OVLDefaultsTemplate#(a) template,
				       String name);
   let defaults_mod = defaults;
   if (isValid(template.msg))
      defaults_mod.msg = validValue(template.msg);

   let value = ((defaults.msg ==  default_msg) ?
		defaults_mod :
      ((template.msg == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"msg\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLCoverageLevel (OVLDefaults#(a) defaults,
						 OVLDefaultsTemplate#(a) template,
						 String name);
   let defaults_mod = defaults;
   if (isValid(template.coverage_level))
      defaults_mod.coverage_level = validValue(template.coverage_level);

   let value = ((defaults.coverage_level == DEFAULT) ?
		defaults_mod :
      ((template.coverage_level == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"coverage_level\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLActionOnNewStart (OVLDefaults#(a) defaults,
						    OVLDefaultsTemplate#(a) template,
						    String name);
   let defaults_mod = defaults;
   if (isValid(template.action_on_new_start))
      defaults_mod.action_on_new_start = validValue(template.action_on_new_start);

   let value = ((defaults.action_on_new_start == DEFAULT) ?
		defaults_mod :
      ((template.action_on_new_start == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"action_on_new_start\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLEdgeType (OVLDefaults#(a) defaults,
					    OVLDefaultsTemplate#(a) template,
					    String name);
   let defaults_mod = defaults;
   if (isValid(template.edge_type))
      defaults_mod.edge_type = validValue(template.edge_type);

   let value = ((defaults.edge_type == DEFAULT) ?
		defaults_mod :
      ((template.edge_type == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"edge_type\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction


function OVLDefaults#(a) updateOVLNecessaryCondition (OVLDefaults#(a) defaults,
						      OVLDefaultsTemplate#(a) template,
						      String name);
   let defaults_mod = defaults;
   if (isValid(template.necessary_condition))
      defaults_mod.necessary_condition = validValue(template.necessary_condition);

   let value = ((defaults.necessary_condition == DEFAULT) ?
		defaults_mod :
      ((template.necessary_condition == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"necessary_condition\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLInactive (OVLDefaults#(a) defaults,
					    OVLDefaultsTemplate#(a) template,
					    String name);
   let defaults_mod = defaults;
   if (isValid(template.inactive))
      defaults_mod.inactive = validValue(template.inactive);

   let value = ((defaults.inactive == DEFAULT) ?
		defaults_mod :
      ((template.inactive == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"inactive\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLNumCks (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.num_cks))
      defaults_mod.num_cks = validValue(template.num_cks);

   let value = ((defaults.num_cks == default_num) ?
		defaults_mod :
      ((template.num_cks == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"num_cks\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLValue (OVLDefaults#(a) defaults,
					 OVLDefaultsTemplate#(a) template,
					 String name)
   provisos(Bounded#(a), Eq#(a));

   let defaults_mod = defaults;
   if (isValid(template.value))
      defaults_mod.value = validValue(template.value);

   let value = ((defaults.value == minBound) ?
		defaults_mod :
      ((template.value == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"value\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMin (OVLDefaults#(a) defaults,
				       OVLDefaultsTemplate#(a) template,
				       String name)
   provisos(Bounded#(a), Eq#(a));

   let defaults_mod = defaults;
   if (isValid(template.min))
      defaults_mod.min = validValue(template.min);

   let value = ((defaults.min == minBound) ?
		defaults_mod :
      ((template.min == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"min\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMax (OVLDefaults#(a) defaults,
				       OVLDefaultsTemplate#(a) template,
				       String name)
   provisos(Bounded#(a), Eq#(a));

   let defaults_mod = defaults;
   if (isValid(template.max))
      defaults_mod.max = validValue(template.max);

   let value = ((defaults.max == maxBound) ?
		defaults_mod :
      ((template.max == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"max\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction


function OVLDefaults#(a) updateOVLMinCks (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.min_cks))
      defaults_mod.min_cks = validValue(template.min_cks);

   let value = ((defaults.min_cks == default_num) ?
		defaults_mod :
      ((template.min_cks == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"min_cks\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMaxCks (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.max_cks))
      defaults_mod.max_cks = validValue(template.max_cks);

   let value = ((defaults.max_cks == default_num) ?
		defaults_mod :
      ((template.max_cks == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"max_cks\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMinAckCycle (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.min_ack_cycle))
      defaults_mod.min_ack_cycle = validValue(template.min_ack_cycle);

   let value = ((defaults.min_ack_cycle == default_num) ?
		defaults_mod :
      ((template.min_ack_cycle == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"min_ack_cycle\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction				

function OVLDefaults#(a) updateOVLMaxAckCycle (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.max_ack_cycle))
      defaults_mod.max_ack_cycle = validValue(template.max_ack_cycle);

   let value = ((defaults.max_ack_cycle == default_num) ?
		defaults_mod :
      ((template.max_ack_cycle == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"max_ack_cycle\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLMaxAckLength (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.max_ack_length))
      defaults_mod.max_ack_length = validValue(template.max_ack_length);

   let value = ((defaults.max_ack_length == default_num) ?
		defaults_mod :
      ((template.max_ack_length == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"max_ack_length\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLReqDrop (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.req_drop))
      defaults_mod.req_drop = validValue(template.req_drop);

   let value = ((defaults.req_drop == default_num) ?
		defaults_mod :
      ((template.req_drop == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"req_drop\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLDeassertCount(OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.deassert_count))
      defaults_mod.deassert_count = validValue(template.deassert_count);

   let value = ((defaults.deassert_count == default_num) ?
		defaults_mod :
      ((template.deassert_count == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"deassert_count\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLDepth (OVLDefaults#(a) defaults,
					  OVLDefaultsTemplate#(a) template,
					  String name);
   let defaults_mod = defaults;
   if (isValid(template.depth))
      defaults_mod.depth = validValue(template.depth);

   let value = ((defaults.depth == default_num) ?
		defaults_mod :
      ((template.depth == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"depth\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction


function OVLDefaults#(a) updateOVLCheckOverlapping (OVLDefaults#(a) defaults,
						    OVLDefaultsTemplate#(a) template,
						    String name);
   let defaults_mod = defaults;
   if (isValid(template.check_overlapping))
      defaults_mod.check_overlapping = validValue(template.check_overlapping);

   let value = ((defaults.check_overlapping == True) ?
		defaults_mod :
      ((template.check_overlapping == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"check_overlapping\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLCheckMissingStart (OVLDefaults#(a) defaults,
						     OVLDefaultsTemplate#(a) template,
						     String name);
   let defaults_mod = defaults;
   if (isValid(template.check_missing_start))
      defaults_mod.check_missing_start = validValue(template.check_missing_start);

   let value = ((defaults.check_missing_start == False) ?
		defaults_mod :
      ((template.check_missing_start == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"check_missing_start\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

function OVLDefaults#(a) updateOVLSimultaneousPushPop (OVLDefaults#(a) defaults,
						     OVLDefaultsTemplate#(a) template,
						     String name);
   let defaults_mod = defaults;
   if (isValid(template.simultaneous_push_pop))
      defaults_mod.simultaneous_push_pop = validValue(template.simultaneous_push_pop);

   let value = ((defaults.simultaneous_push_pop == True) ?
		defaults_mod :
      ((template.simultaneous_push_pop == Invalid) ?
       error(strConcat("Error:  Attempt to set the value of \"simultaneous_push_pop\" which is not a valid parameter for ", name)) :
       defaults));

   return value;

endfunction

////////////////////////////////////////////////////////////////////////////////
//
// Four interfaces are defined for use with these assertion modules:
//
//  1) AssertTest_IFC
//
//     o has a single Action method "test" that takes a single polymorphic
//       argument.
//     o good for invariant assertions that check a test expression on
//       every clock cycle (for instance bsv_assert_one_hot)
//
//  2) AssertSampleTest_IFC
//
//     o has an Action method "sample" and an Action method "test"
//     o each method takes a single argument (sample is of type Bool, test is
//       polymorphic)
//     o same as AssertTest_IFC but the test expression is only checked when
//       sample is asserted.
//
//  3) AssertStartTest_IFC
//
//     o has an Action method "start" and an Action method "test"
//     o each method takes a single argument (start is of type Bool, test is
//       polymorphic)
//     o used to check a test expression only subsequent to a start_event.
//
//  4) AssertStartStopTest_IFC
//
//     o has an Action method "start", and Action method stop, and an Action
//       method "test"
//     o each method takes a single argument (start and stop are of type Bool,
//       test is polymorphic)
//     o used to check a test expression between a start_event and an end_event.
//
//
////////////////////////////////////////////////////////////////////////////////

interface AssertTest_IFC #(type a);

   method Action test(a value);

endinterface

interface VAssertTest_IFC #(type n);

   method Action test(Bit#(n) value);

endinterface

interface AssertSampleTest_IFC #(type a);

   method Action sample(Bool value);
   method Action test(a value);

endinterface

interface VAssertSampleTest_IFC #(type n);

   method Action sample(Bit#(1) value);
   method Action test(Bit#(n) value);

endinterface

interface AssertStartTest_IFC #(type a);

   method Action start(Bool value);
   method Action test(a value);

endinterface

interface VAssertStartTest_IFC #(type n);

   method Action start(Bit#(1) value);
   method Action test(Bit#(n) value);

endinterface

interface AssertStartStopTest_IFC #(type a);

   method Action start(Bool value);
   method Action stop(Bool value);
   method Action test(a value);

endinterface

interface VAssertStartStopTest_IFC #(type n);

   method Action start(Bit#(1) value);
   method Action stop(Bit#(1) value);
   method Action test(Bit#(n) value);

endinterface

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_ALWAYS
//
// bsv_assert_always - An invariant concurrent assertion to ensure that its
//                     argument always evaluates TRUE.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_always_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_always#(OVLDefaults#(Bool) defaults) (AssertTest_IFC#(Bool));

   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_always_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_always");

   let _m = liftModule(v_assert_always(defaults_final));
   VAssertTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_always =
module v_assert_always#(OVLDefaults#(Bool) defaults) (VAssertTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_ALWAYS_ON_EDGE
//
// bsv_assert_always_on_edge - Checks that the test expression evaluates true
//                             whenever the sample method is asserted.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_always_on_edge_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.edge_type      = Valid(OVL_NOEDGE);

   return defaults;

endfunction

module bsv_assert_always_on_edge#(OVLDefaults#(Bool) defaults) (AssertSampleTest_IFC#(Bool));

   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_always_on_edge_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_always_on_edge");

   let _m = liftModule(v_assert_always_on_edge(defaults_final));
   VAssertSampleTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method sample(x) ;  return (_r.sample)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_always_on_edge =
module v_assert_always_on_edge#(OVLDefaults#(Bool) defaults) (VAssertSampleTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter edge_type      = pack(defaults.edge_type);

   method sample(sampling_event) enable((* inhigh *)EN_sample);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (sample, test) CF (sample, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_CHANGE
//
//  bsv_assert_change - Checks that once the start method is asserted, within
//                     "num_cks" cycles the test expression will change value.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_change_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.action_on_new_start = Valid(OVL_IGNORE_NEW_START);
   defaults.num_cks             = Valid(1);

   return defaults;

endfunction

module bsv_assert_change#(OVLDefaults#(a) defaults) (AssertStartTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_change_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_change");

   let _m = liftModule(v_assert_change(defaults_final, valueOf(sa)));
   VAssertStartTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_change =
module v_assert_change#(OVLDefaults#(a) defaults, Integer width)(VAssertStartTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width               = width;
   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter action_on_new_start = pack(defaults.action_on_new_start);
   parameter num_cks             = pack(defaults.num_cks);

   method start(start_event) enable((* inhigh *)EN_start);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule


////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_DECREMENT
//
//  bsv_assert_decrement - An invariant concurrent assertion to ensure that the test
//                         expression always decreases by the value of VALUE.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_decrement_defaults ()
   provisos (Literal#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.value               = Valid(1);

   return defaults;

endfunction

module bsv_assert_decrement#(OVLDefaults#(a) defaults)(AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Literal#(a), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_decrement_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_decrement");

   let _m = liftModule(v_assert_decrement(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_decrement =
module v_assert_decrement#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;
   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter value          = pack(defaults.value);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_DELTA
//
//  bsv_assert_delta - An invariant concurrent assertion to ensure that the test
//                     expression always changes by at least MIN and at most MAX.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_delta_defaults ()
   provisos (Literal#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.min            = Valid(1);
   defaults.max            = Valid(1);

   return defaults;

endfunction

module bsv_assert_delta#(OVLDefaults#(a) defaults)(AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Literal#(a), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_delta_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_delta");

   let _m = liftModule(v_assert_delta(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_delta =
module v_assert_delta#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter min            = pack(defaults.min);
   parameter max            = pack(defaults.max);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_EVEN_PARITY
//
// bsv_assert_even_parity - An invariant concurrent assertion to ensure that
//                          an even number of bits in the test expression are
//                          active high.
//
//////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_even_parity_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_even_parity#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_even_parity_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_even_parity");

   let _m = liftModule(v_assert_even_parity(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_even_parity =
module v_assert_even_parity#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule


////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_FRAME
//
//  bsv_assert_frame - Checks that once the start method is asserted, the test
//                     expression evaluates true not before MIN clock cycles
//                     and not after MAX clock cycles.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_frame_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.action_on_new_start = Valid(OVL_IGNORE_NEW_START);
   defaults.min_cks        = Valid(0);
   defaults.max_cks        = Valid(0);

   return defaults;

endfunction

module bsv_assert_frame#(OVLDefaults#(Bool) defaults) (AssertStartTest_IFC#(Bool));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_frame_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_frame");

   let _m = liftModule(v_assert_frame(defaults_final));
   VAssertStartTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_frame =
module v_assert_frame#(OVLDefaults#(Bool) defaults) (VAssertStartTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter action_on_new_start = pack(defaults.action_on_new_start);
   parameter min_cks             = pack(defaults.min_cks);
   parameter max_cks             = pack(defaults.max_cks);

   method start(start_event) enable((* inhigh *)EN_start);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_HANDSHAKE
//
//  bsv_assert_handshake - Similar to assert_frame except that requirements as to
//                         how if req must remain active until ack arrives and
//                         if so how long afterack it must remain active are
//                         controllable by checker parameters.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_handshake_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.max_ack_length = Valid(0);
   defaults.req_drop       = Valid(0);
   defaults.deassert_count = Valid(0);
   defaults.min_ack_cycle  = Valid(0);
   defaults.max_ack_cycle  = Valid(0);

   return defaults;

endfunction

module bsv_assert_handshake#(OVLDefaults#(Bool) defaults) (AssertStartTest_IFC#(Bool));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_handshake_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_handshake");

   let _m = liftModule(v_assert_handshake(defaults_final));
   VAssertStartTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_handshake =
module v_assert_handshake#(OVLDefaults#(Bool) defaults) (VAssertStartTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter max_ack_length      = pack(defaults.max_ack_length);
   parameter req_drop            = pack(defaults.req_drop);
   parameter deassert_count      = pack(defaults.deassert_count);

   parameter min_ack_cycle       = pack(defaults.min_ack_cycle);
   parameter max_ack_cycle       = pack(defaults.max_ack_cycle);


   method start(req) enable((* inhigh *)EN_start);
   method test(ack)  enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_IMPLICATION
//
//  bsv_assert_implication - Checks that once the start method is asserted, the
//
//
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_implication_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_implication#(OVLDefaults#(Bool) defaults) (AssertStartTest_IFC#(Bool));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_implication_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_implication");

   let _m = liftModule(v_assert_implication(defaults_final));
   VAssertStartTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_implication =
module v_assert_implication#(OVLDefaults#(Bool) defaults) (VAssertStartTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method start(antecedent_expr) enable((* inhigh *)EN_start);
   method test(consequent_expr)  enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_INCREMENT
//
//  bsv_assert_increment - An invariant concurrent assertion to ensure that the test
//                         expression always increases by the value of VALUE.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_increment_defaults ()
   provisos (Literal#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.value          = Valid(1);

   return defaults;

endfunction

module bsv_assert_increment#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Literal#(a), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_increment_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_increment");


   let _m = liftModule(v_assert_increment(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_increment =
module v_assert_increment#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;
   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter value          = pack(defaults.value);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_NEVER
//
// bsv_assert_never - An invariant concurrent assertion to ensure that its
//                    argument never evaluates TRUE.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_never_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_never#(OVLDefaults#(Bool) defaults) (AssertTest_IFC#(Bool));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_never_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_never");

   let _m = liftModule(v_assert_never(defaults_final));
   VAssertTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_never =
module v_assert_never#(OVLDefaults#(Bool) defaults) (VAssertTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_ODD_PARITY
//
// bsv_assert_odd_parity - An invariant concurrent assertion to ensure that
//                         an odd number of bits in the test expression are
//                         active high.
//
//////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_odd_parity_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_odd_parity#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_odd_parity_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_odd_parity");

   let _m = liftModule(v_assert_odd_parity(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_odd_parity =
module v_assert_odd_parity#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule



////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_NEXT
//
//  bsv_assert_next - Checks that the start method is asserted, after
//                    "num_cks" cycles the test method will be asserted, or in
//                    logical terms, where X denotes the next cycle operator,
//                    "start_event  => X^n (test_expr)"
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_next_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.num_cks             = Valid(1);
   defaults.check_overlapping   = Valid(True);
   defaults.check_missing_start = Valid(False);

   return defaults;

endfunction


module bsv_assert_next#(OVLDefaults#(Bool) defaults)(AssertStartTest_IFC#(Bool));

   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_next_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_next");

   let _m = liftModule(v_assert_next(defaults_final));
   VAssertStartTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_next =
module v_assert_next#(OVLDefaults#(Bool) defaults)(VAssertStartTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter num_cks             = pack(defaults.num_cks);
   parameter check_overlapping   = pack(defaults.check_overlapping);
   parameter check_missing_start = pack(defaults.check_missing_start);

   method start(start_event) enable((* inhigh *)EN_start);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//        ASSERT_NO_OVERFLOW
//
// bsv_assert_no_overflow - An invariant concurrent assertion to ensure that:
//                          After an expression has reached a MAX limit
//                          value, the expression does not subsequently exceed
//                          the MAX limit or reach a MIN limit value.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_no_overflow_defaults ()
   provisos (Bounded#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.min            = Valid(minBound);
   defaults.max            = Valid(maxBound);

   return defaults;

endfunction


module bsv_assert_no_overflow#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_no_overflow_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_no_overflow");

   let _m = liftModule(v_assert_no_overflow(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_no_overflow =
module v_assert_no_overflow#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   parameter min            = pack(defaults.min);
   parameter max            = pack(defaults.max);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//        ASSERT_NO_UNDERFLOW
//
// bsv_assert_no_underflow - An invariant concurrent assertion to ensure that:
//                           After an expression has reached a MIN limit
//                           value, the expression does not subsequently
//                           fall below the MIN limit or reach a MAX limit value.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_no_underflow_defaults ()
   provisos (Bounded#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.min            = Valid(minBound);
   defaults.max            = Valid(maxBound);

   return defaults;

endfunction

module bsv_assert_no_underflow#(OVLDefaults#(a) defaults)(AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_no_underflow_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_no_underflow");


   let _m = liftModule(v_assert_no_underflow(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_no_underflow =
module v_assert_no_underflow#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   parameter min            = pack(defaults.min);
   parameter max            = pack(defaults.max);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_ONE_COLD
//
// bsv_assert_one_cold - An invariant concurrent assertion to ensure that
//                       exactly one bit of a variable is active low.
//
//////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_one_cold_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.inactive = Valid(OVL_ONE_COLD);

   return defaults;

endfunction

module bsv_assert_one_cold#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_one_cold_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_one_cold");

   let _m = liftModule(v_assert_one_cold(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_one_cold =
module v_assert_one_cold#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   parameter inactive = pack(defaults.inactive);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_ONE_HOT
//
// bsv_assert_one_hot - An invariant concurrent assertion to ensure that
//                      exactly one bit of a variable is active high.
//
//////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_one_hot_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_one_hot#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_one_hot_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_one_hot");

   let _m = liftModule(v_assert_one_hot(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_one_hot =
module v_assert_one_hot#(OVLDefaults#(a) defaults, Integer width) (VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_PROPOSITION
//
// bsv_assert_proposition - Like assert_always except that the test expression
//                          is not sampled by the clock.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_proposition_defaults();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_proposition#(OVLDefaults#(Bool) defaults) (AssertTest_IFC#(Bool));
   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_proposition_defaults();
   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_always");
   let _m = liftModule(v_assert_proposition(defaults_final));
   VAssertTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_proposition =
module v_assert_proposition#(OVLDefaults#(Bool) defaults) (VAssertTest_IFC#(1));


   default_clock (); // syntax for no clock port.
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_RANGE
//
//  bsv_assert_range - An invariant concurrent assertion to ensure that an
//                     expression is always within a valid MIN limit and MAX
//                     limit range.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_range_defaults ()
   provisos (Bounded#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.min            = Valid(minBound);
   defaults.max            = Valid(maxBound);

   return defaults;

endfunction

module bsv_assert_range#(OVLDefaults#(a) defaults)(AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_range_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_range");

   let _m = liftModule(v_assert_range(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_range =
module v_assert_range#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   parameter min            = pack(defaults.min);
   parameter max            = pack(defaults.max);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_TIME
//
//  bsv_assert_time - Checks that once the start method is asserted, the
//                        test expression does not change value within "num_cks"
//                        cycles.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_time_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.action_on_new_start = Valid(OVL_IGNORE_NEW_START);
   defaults.num_cks             = Valid(1);

   return defaults;

endfunction

module bsv_assert_time#(OVLDefaults#(Bool) defaults)(AssertStartTest_IFC#(Bool));

   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_time_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_time");


   let _m = liftModule(v_assert_time(defaults_final));
   VAssertStartTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_time =
module v_assert_time#(OVLDefaults#(Bool) defaults)(VAssertStartTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter action_on_new_start = pack(defaults.action_on_new_start);
   parameter num_cks             = pack(defaults.num_cks);

   method start(start_event) enable((* inhigh *)EN_start);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_UNCHANGE
//
//  bsv_assert_unchange - Checks that once the start method is asserted, the
//                        test expression does not change value within "num_cks"
//                        cycles.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_unchange_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.action_on_new_start = Valid(OVL_IGNORE_NEW_START);
   defaults.num_cks             = Valid(1);

   return defaults;

endfunction

module bsv_assert_unchange#(OVLDefaults#(a) defaults)(AssertStartTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_unchange_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_unchange");

   let _m = liftModule(v_assert_unchange(defaults_final, valueOf(sa)));
   VAssertStartTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_unchange =
module v_assert_unchange#(OVLDefaults#(a) defaults, Integer width)(VAssertStartTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width               = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);
   parameter action_on_new_start = pack(defaults.action_on_new_start);

   parameter num_cks             = pack(defaults.num_cks);

   method start(start_event) enable((* inhigh *)EN_start);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_WIDTH
//
//  bsv_assert_width - An invariant concurrent assertion to ensure that when the
//                     test expression goes high it stays high for at least MIN
//                     and at most MAX clock cycles.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_width_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   defaults.min_cks        = Valid(1);
   defaults.max_cks        = Valid(1);

   return defaults;

endfunction

module bsv_assert_width#(OVLDefaults#(Bool) defaults)(AssertTest_IFC#(Bool));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_frame_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_frame");

   let _m = liftModule(v_assert_width(defaults_final));
   VAssertTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_width =
module v_assert_width#(OVLDefaults#(Bool) defaults)(VAssertTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   parameter min_cks             = pack(defaults.min_cks);
   parameter max_cks             = pack(defaults.max_cks);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_WIN_CHANGE
//
//  bsv_assert_win_change - Checks that once the start method is asserted, the
//                          test expression will change value prior to and
//                          including when the stop method is asserted.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_win_change_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_win_change#(OVLDefaults#(a) defaults) (AssertStartStopTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_win_change_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_win_change");

   let _m = liftModule(v_assert_win_change(defaults_final, valueOf(sa)));
   VAssertStartStopTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method stop(x) ;  return (_r.stop)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_win_change =
module v_assert_win_change#(OVLDefaults#(a) defaults, Integer width)(VAssertStartStopTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method start(start_event) enable((* inhigh *)EN_start);
   method stop(end_event)    enable((* inhigh *)EN_stop);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, stop, test) CF (start, stop, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_WIN_UNCHANGE
//
//  bsv_assert_win_unchange - Checks that once the start method is asserted, the
//                            test expression will not change value prior to and
//                            including when the stop method is asserted.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_win_unchange_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_win_unchange#(OVLDefaults#(a) defaults) (AssertStartStopTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_win_unchange_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_win_unchange");

   let _m = liftModule(v_assert_win_unchange(defaults_final, valueOf(sa)));
   VAssertStartStopTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method stop(x) ;  return (_r.stop)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_win_unchange =
module v_assert_win_unchange#(OVLDefaults#(a) defaults, Integer width)(VAssertStartStopTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method start(start_event) enable((* inhigh *)EN_start);
   method stop(end_event)    enable((* inhigh *)EN_stop);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, stop, test) CF (start, stop, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
///
//       ASSERT_WINDOW
//
//  bsv_assert_window - Same as assert_min_unchange except that the checker does
//                      not evaluate test expression until one clock cycle after
//                      start_event.
//
////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_window_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_window#(OVLDefaults#(Bool) defaults) (AssertStartStopTest_IFC#(Bool));

   OVLDefaultsTemplate#(Bool) defaults_template = create_assert_window_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_window");

   let _m = liftModule(v_assert_window(defaults_final));
   VAssertStartStopTest_IFC#(1) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method stop(x) ;  return (_r.stop)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_window =
module v_assert_window#(OVLDefaults#(Bool) defaults) (VAssertStartStopTest_IFC#(1));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method start(start_event) enable((* inhigh *)EN_start);
   method stop(end_event)    enable((* inhigh *)EN_stop);
   method test(test_expr)    enable((* inhigh *)EN_test);

   schedule (start, stop, test) CF (start, stop, test);
endmodule

////////////////////////////////////////////////////////////////////////////////
//
//       ASSERT_ZERO_ONE_HOT
//
// bsv_assert_zero_one_hot - An invariant concurrent assertion to ensure that
//                           exactly one bit of a variable is active high or
//                           that the variable is zero.
//
//////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_zero_one_hot_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_zero_one_hot#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_zero_one_hot_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_zero_one_hot");

   let _m = liftModule(v_assert_zero_one_hot(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_zero_one_hot =
module v_assert_zero_one_hot#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

      schedule (test) CF (test);

endmodule

////////////////////////////////////////////////////////////////////////////////////
///
//    ASSERT_CYCLE_SEQUENCE
//
//    bsv_assert_cycle_sequence- Ensures that if a specified necessary condition
//                               occurs,it is followed by a specified sequence
//								 of events.
//
///////////////////////////////////////////////////////////////////////////////////
                			
function OVLDefaultsTemplate#(a) create_assert_cycle_sequence_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);
   defaults.necessary_condition = Valid(OVL_TRIGGER_ON_MOST_PIPE);

   return defaults;

endfunction

module bsv_assert_cycle_sequence#(OVLDefaults#(a) defaults) (AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Add#(ignore, 2, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_cycle_sequence_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_cycle_sequence");

   let _m = liftModule(v_assert_cycle_sequence(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_cycle_sequence =
module v_assert_cycle_sequence#(OVLDefaults#(a) defaults, Integer num_cks) (VAssertTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter necessary_condition = pack(defaults.necessary_condition);
   parameter num_cks = num_cks;

   method test(event_sequence) enable((* inhigh *)EN_test);

   schedule (test) CF (test);

endmodule

/////////////////////////////////////////////////////////////////////////////////////////////////////
//
//      ASSERT_NEVER_UNKNOWN
//
//      bsv_assert_never_unknown- Ensures that the value of a specified expression contains only
//                                0 and 1 bits when a qualifying expression is TRUE.
//
//
/////////////////////////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_never_unknown_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_never_unknown#(OVLDefaults#(a) defaults) (AssertStartTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_never_unknown_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_never_unknown");

   let _m = liftModule(v_assert_never_unknown(defaults_final, valueOf(sa)));
   VAssertStartTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_never_unknown =
module v_assert_never_unknown#(OVLDefaults#(a) defaults, Integer width)(VAssertStartTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width               = width;
   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method start(qualifier) enable((* inhigh *)EN_start);
   method test(test_expr)  enable((* inhigh *)EN_test);

   schedule (start, test) CF (start, test);

endmodule

/////////////////////////////////////////////////////////////////////////////////////////////////////////
//
//            ASSERT_NO_TRANSITION
//
//            bsv_assert_no_transition- Ensures that the value of a specified expression does not
//                                      transition from a start state to the specified next state.
//
//
///////////////////////////////////////////////////////////////////////////////////////////////////////

interface AssertTransitionTest_IFC #(type a);
    method Action test(a value);
	method Action start(a value);
	method Action next(a value);
endinterface

interface VAssertTransitionTest_IFC #(type n);
    method Action test(Bit#(n) value);
	method Action start(Bit#(n) value);
	method Action next(Bit#(n) value);
endinterface

function OVLDefaultsTemplate#(a) create_assert_no_transition_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_no_transition#(OVLDefaults#(a) defaults) (AssertTransitionTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_no_transition_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_no_transition");

   let _m = liftModule(v_assert_no_transition(defaults_final, valueOf(sa)));
   VAssertTransitionTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method next(x) ;  return (_r.next)(pack(x));
   endmethod

endmodule

import "BVI" assert_no_transition =
module v_assert_no_transition#(OVLDefaults#(a) defaults, Integer width)(VAssertTransitionTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method test(test_expr)       enable((* inhigh *)EN_test);
   method start(start_state)    enable((* inhigh *)EN_start);
   method next(next_state)      enable((* inhigh *)EN_next);

   schedule (test, start, next) CF (test, start, next);

endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////
//
//             ASSERT_TRANSITION
//
//             bsv_assert_transition- Ensures that the value of a specified expression transitions
//                                    properly from a start state to the specified next state.
//
//
///////////////////////////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_transition_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_transition#(OVLDefaults#(a) defaults) (AssertTransitionTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_transition_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_transition");

   let _m = liftModule(v_assert_transition(defaults_final, valueOf(sa)));
   VAssertTransitionTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

   method start(x) ;  return (_r.start)(pack(x));
   endmethod

   method next(x) ;  return (_r.next)(pack(x));
   endmethod

endmodule

import "BVI" assert_transition =
module v_assert_transition#(OVLDefaults#(a) defaults, Integer width)(VAssertTransitionTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method test(test_expr)       enable((* inhigh *)EN_test);
   method start(start_state)    enable((* inhigh *)EN_start);
   method next(next_state)      enable((* inhigh *)EN_next);

   schedule (test, start, next) CF (test, start, next);

endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////
//
//        ASSERT_QUIESCENT_STATE
//
//        bsv_assert_quiescent_state- Ensures that the value of a specified state expression equals a
//                                    corresponding check value if a specified sample event has
//                                    transitioned to TRUE.
//
//
///////////////////////////////////////////////////////////////////////////////////////////////////////

interface AssertQuiescentTest_IFC #(type a);
    method Action sample(Bool value);
	method Action state(a value);
	method Action check(a value);
endinterface

interface VAssertQuiescentTest_IFC #(type n);
    method Action sample(Bit#(1) value);
	method Action state(Bit#(n) value);
	method Action check(Bit#(n) value);
endinterface


function OVLDefaultsTemplate#(a) create_assert_quiescent_state_defaults ();

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_quiescent_state#(OVLDefaults#(a) defaults) (AssertQuiescentTest_IFC#(a))
   provisos (Bits#(a, sa), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_quiescent_state_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_quiescent_state");

   let _m = liftModule(v_assert_quiescent_state(defaults_final, valueOf(sa)));
   VAssertQuiescentTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method sample(x) ;  return (_r.sample)(pack(x));
   endmethod

   method state(x) ;  return (_r.state)(pack(x));
   endmethod

   method check(x) ;  return (_r.check)(pack(x));
   endmethod

endmodule

import "BVI" assert_quiescent_state =
module v_assert_quiescent_state#(OVLDefaults#(a) defaults, Integer width)(VAssertQuiescentTest_IFC#(n));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter width = width;

   parameter severity_level      = pack(defaults.severity_level);
   parameter property_type       = pack(defaults.property_type);
   parameter msg                 = defaults.msg;
   parameter coverage_level      = pack(defaults.coverage_level);

   method sample(sample_event) enable((* inhigh *)EN_sample);
   method state(state_expr)    enable((* inhigh *)EN_state);
   method check(check_value)   enable((* inhigh *)EN_check);

   schedule (sample, state, check) CF (sample, state, check);

endmodule

///////////////////////////////////////////////////////////////////////////////////////////////////////
//
//      ASSERT_NEVER_UNKNOWN_ASYNC
//
//      bsv_assert_never_unknown_async- Ensures that the value of a specified expression always contains
//                                      only 0 and 1 bits
//
///////////////////////////////////////////////////////////////////////////////////////////////////////

function OVLDefaultsTemplate#(a) create_assert_never_unknown_async_defaults ()
   provisos (Literal#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);

   return defaults;

endfunction

module bsv_assert_never_unknown_async#(OVLDefaults#(a) defaults)(AssertTest_IFC#(a))
   provisos (Bits#(a, sa), Literal#(a), Bounded#(a), Eq#(a));

   OVLDefaultsTemplate#(a) defaults_template = create_assert_never_unknown_async_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_never_unknown_async");

   let _m = liftModule(v_assert_never_unknown_async(defaults_final, valueOf(sa)));
   VAssertTest_IFC#(sa) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method test(x) ;  return (_r.test)(pack(x));
   endmethod

endmodule

import "BVI" assert_never_unknown_async =
module v_assert_never_unknown_async#(OVLDefaults#(a) defaults, Integer width)(VAssertTest_IFC#(n))
   provisos (Bits#(a, sa));

   default_clock ();
   default_reset reset (reset_n);

   parameter width = width;
   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);

   method test(test_expr) enable((* inhigh *)EN_test);

   schedule (test) CF (test);

endmodule

//////////////////////////////////////////////////////////////////////////////////////////////////
//
//         ASSERT_FIFO_INDEX
//
//         bsv_assert_fifo_index- Ensures that a FIFO-type structure never overflows or underflows.
//                                This checker can be configured to support multiple pushes
//                                (FIFO writes) and pops (FIFO reads) during the same clock cycle.
//
//
/////////////////////////////////////////////////////////////////////////////////////////////////

interface AssertFifoTest_IFC #(type a, type b);
   method Action push(a value);
   method Action pop(b value);
endinterface

interface VAssertFifoTest_IFC #(type n, type m);
   method Action push(Bit#(n) value);
   method Action pop(Bit#(m) value);
endinterface

function OVLDefaultsTemplate#(a) create_assert_fifo_index_defaults ()
   provisos (Bounded#(a));

   let defaults = mkOVLDefaultsTemplate;

   defaults.severity_level = Valid(OVL_ERROR);
   defaults.property_type  = Valid(OVL_ASSERT);
   defaults.msg            = Valid("VIOLATION");
   defaults.coverage_level = Valid(OVL_COVER_ALL);
   defaults.depth          = Valid(1);
   defaults.simultaneous_push_pop = Valid(True);

  return defaults;

endfunction

module bsv_assert_fifo_index#(OVLDefaults#(Bit#(0)) defaults) (AssertFifoTest_IFC#(a, b))
   provisos (Bits#(a, sa), Bits#(b, sb));

   OVLDefaultsTemplate#(Bit#(0)) defaults_template = create_assert_fifo_index_defaults();

   let defaults_final = updateOVLDefaults(defaults,
					  defaults_template,
					  "bsv_assert_fifo_index");

   let _m = liftModule(v_assert_fifo_index(defaults_final, valueOf(sa), valueOf(sb)));
   VAssertFifoTest_IFC#(sa, sb) _r();
   _m __(_r); // the "__" makes this instantiation anonymous

   method push(x) ;  return (_r.push)(pack(x));
   endmethod

   method pop(x) ;  return (_r.pop)(pack(x));
   endmethod

endmodule

import "BVI" assert_fifo_index =
module v_assert_fifo_index#(OVLDefaults#(Bit#(0)) defaults, Integer push_width, Integer pop_width) (VAssertFifoTest_IFC#(n, m));

   default_clock clk (clk);
   default_reset reset (reset_n);

   parameter push_width = push_width;
   parameter pop_width  = pop_width;

   parameter depth          = pack(defaults.depth);
   parameter severity_level = pack(defaults.severity_level);
   parameter property_type  = pack(defaults.property_type);
   parameter msg            = defaults.msg;
   parameter coverage_level = pack(defaults.coverage_level);
   parameter simultaneous_push_pop = pack(defaults.simultaneous_push_pop);

   method push(push) enable((* inhigh *)EN_push);
   method pop(pop)   enable((* inhigh *)EN_pop);

   schedule (push, pop) CF (push, pop);
endmodule

endpackage
