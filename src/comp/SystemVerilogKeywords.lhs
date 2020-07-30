> {-# OPTIONS_GHC -Wall -fno-warn-unused-matches -fno-warn-name-shadowing #-}

System Verilog keywords

CAVEAT: you should run checkSystemVerilogKeywords after changing this file.

> module SystemVerilogKeywords(SV_Keyword(..), SV_Version(..),
>                              SV_Symbol(..),
>                              svKeywordTable,
>                              svSymbolTable,
>                              svSymbolChars,
>                              checkSystemVerilogKeywords) where

> import Data.List(sort,group,(\\),nub)
> import Control.Monad(when)
> import System.IO(hPutStrLn, stderr)
> import System.Exit(exitWith, ExitCode(..))

A datatype for SystemVerilog keywords, complete with printed
representation, and language version introduced.

Keyword sources (should we wish to parse a subset):

> data SV_Version = Verilog2001 | SystemVerilog30 | SystemVerilog31
>                 | SystemVerilog31a | Bluespec38
>                   deriving (Show)

Data type declaration for the keywords:

> data SV_Keyword
>     = SV_KW_alias
>     | SV_KW_always
>     | SV_KW_always_comb
>     | SV_KW_always_ff
>     | SV_KW_always_latch
>     | SV_KW_and
>     | SV_KW_assert
>     | SV_KW_assert_strobe
>     | SV_KW_assign
>     | SV_KW_assume
>     | SV_KW_automatic
>     | SV_KW_before
>     | SV_KW_begin
>     | SV_KW_bind
>     | SV_KW_bins
>     | SV_KW_binsof
>     | SV_KW_bit
>     | SV_KW_break
>     | SV_KW_buf
>     | SV_KW_bufif0
>     | SV_KW_bufif1
>     | SV_KW_byte
>     | SV_KW_case
>     | SV_KW_casex
>     | SV_KW_casez
>     | SV_KW_cell
>     | SV_KW_chandle
>     | SV_KW_class
>     | SV_KW_clocking
>     | SV_KW_cmos
>     | SV_KW_config
>     | SV_KW_const
>     | SV_KW_constraint
>     | SV_KW_context
>     | SV_KW_continue
>     | SV_KW_cover
>     | SV_KW_covergroup
>     | SV_KW_coverpoint
>     | SV_KW_cross
>     | SV_KW_deassign
>     | SV_KW_default
>     | SV_KW_defparam
>     | SV_KW_design
>     | SV_KW_disable
>     | SV_KW_dist
>     | SV_KW_do
>     | SV_KW_edge
>     | SV_KW_else
>     | SV_KW_end
>     | SV_KW_endcase
>     | SV_KW_endclass
>     | SV_KW_endclocking
>     | SV_KW_endconfig
>     | SV_KW_endfunction
>     | SV_KW_endgenerate
>     | SV_KW_endgroup
>     | SV_KW_endinterface
>     | SV_KW_endmodule
>     | SV_KW_endpackage
>     | SV_KW_endprimitive
>     | SV_KW_endprogram
>     | SV_KW_endproperty
>     | SV_KW_endspecify
>     | SV_KW_endsequence
>     | SV_KW_endtable
>     | SV_KW_endtask
>     | SV_KW_enum
>     | SV_KW_event
>     | SV_KW_expect
>     | SV_KW_export
>     | SV_KW_extends
>     | SV_KW_extern
>     | SV_KW_final
>     | SV_KW_first_match
>     | SV_KW_for
>     | SV_KW_force
>     | SV_KW_foreach
>     | SV_KW_forever
>     | SV_KW_fork
>     | SV_KW_forkjoin
>     | SV_KW_function
>     | SV_KW_generate
>     | SV_KW_genvar
>     | SV_KW_highz0
>     | SV_KW_highz1
>     | SV_KW_if
>     | SV_KW_iff
>     | SV_KW_ifnone
>     | SV_KW_ignore_bins
>     | SV_KW_illegal_bins
>     | SV_KW_import
>     | SV_KW_incdir
>     | SV_KW_include
>     | SV_KW_initial
>     | SV_KW_inout
>     | SV_KW_input
>     | SV_KW_inside
>     | SV_KW_instance
>     | SV_KW_int
>     | SV_KW_integer
>     | SV_KW_interface
>     | SV_KW_intersect
>     | SV_KW_join
>     | SV_KW_join_any
>     | SV_KW_join_none
>     | SV_KW_large
>     | SV_KW_liblist
>     | SV_KW_library
>     | SV_KW_local
>     | SV_KW_localparam
>     | SV_KW_logic
>     | SV_KW_longint
>     | SV_KW_macromodule
>     | SV_KW_match
>     | SV_KW_matches
>     | SV_KW_medium
>     | SV_KW_modport
>     | SV_KW_module
>     | SV_KW_nand
>     | SV_KW_negedge
>     | SV_KW_new
>     | SV_KW_nmos
>     | SV_KW_nor
>     | SV_KW_noshowcancelled
>     | SV_KW_not
>     | SV_KW_notif0
>     | SV_KW_notif1
>     | SV_KW_null
>     | SV_KW_or
>     | SV_KW_output
>     | SV_KW_package
>     | SV_KW_packed
>     | SV_KW_parameter
>     | SV_KW_pmos
>     | SV_KW_posedge
>     | SV_KW_primitive
>     | SV_KW_priority
>     | SV_KW_program
>     | SV_KW_property
>     | SV_KW_protected
>     | SV_KW_pull0
>     | SV_KW_pull1
>     | SV_KW_pulldown
>     | SV_KW_pullup
>     | SV_KW_pulsestyle_onevent
>     | SV_KW_pulsestyle_ondetect
>     | SV_KW_pure
>     | SV_KW_rand
>     | SV_KW_randc
>     | SV_KW_randcase
>     | SV_KW_randsequence
>     | SV_KW_rcmos
>     | SV_KW_real
>     | SV_KW_realtime
>     | SV_KW_ref
>     | SV_KW_reg
>     | SV_KW_release
>     | SV_KW_repeat
>     | SV_KW_return
>     | SV_KW_rnmos
>     | SV_KW_rpmos
>     | SV_KW_rtran
>     | SV_KW_rtranif0
>     | SV_KW_rtranif1
>     | SV_KW_scalared
>     | SV_KW_sequence
>     | SV_KW_shortint
>     | SV_KW_shortreal
>     | SV_KW_showcancelled
>     | SV_KW_signed
>     | SV_KW_small
>     | SV_KW_solve
>     | SV_KW_specify
>     | SV_KW_specparam
>     | SV_KW_static
>     | SV_KW_string
>     | SV_KW_strong0
>     | SV_KW_strong1
>     | SV_KW_struct
>     | SV_KW_super
>     | SV_KW_supply0
>     | SV_KW_supply1
>     | SV_KW_table
>     | SV_KW_tagged
>     | SV_KW_task
>     | SV_KW_this
>     | SV_KW_throughout
>     | SV_KW_time
>     | SV_KW_timeprecision
>     | SV_KW_timeunit
>     | SV_KW_tran
>     | SV_KW_tranif0
>     | SV_KW_tranif1
>     | SV_KW_tri
>     | SV_KW_tri0
>     | SV_KW_tri1
>     | SV_KW_triand
>     | SV_KW_trior
>     | SV_KW_trireg
>     | SV_KW_type
>     | SV_KW_typedef
>     | SV_KW_union
>     | SV_KW_unique
>     | SV_KW_unsigned
>     | SV_KW_use
>     | SV_KW_var
>     | SV_KW_vectored
>     | SV_KW_virtual
>     | SV_KW_void
>     | SV_KW_wait
>     | SV_KW_wait_order
>     | SV_KW_wand
>     | SV_KW_weak0
>     | SV_KW_weak1
>     | SV_KW_while
>     | SV_KW_wildcard
>     | SV_KW_wire
>     | SV_KW_with
>     | SV_KW_within
>     | SV_KW_wor
>     | SV_KW_xnor
>     | SV_KW_xor
>     -- Bluespec/SystemVerilog keywords
>     | SV_KW_action
>     | SV_KW_endaction
>     | SV_KW_actionvalue
>     | SV_KW_endactionvalue
>     | SV_KW_deriving
>     | SV_KW_endinstance
>     | SV_KW_let
>     | SV_KW_method
>     | SV_KW_endmethod
>     | SV_KW_par
>     | SV_KW_endpar
>     | SV_KW_abortif
>     | SV_KW_provisos
>     | SV_KW_rule
>     | SV_KW_endrule
>     | SV_KW_rules
>     | SV_KW_endrules
>     | SV_KW_seq
>     | SV_KW_endseq
>     | SV_KW_goto
>--     | SV_KW_schedule
>     | SV_KW_typeclass
>     | SV_KW_endtypeclass
>--     | SV_KW_clock
>--     | SV_KW_reset
>--     | SV_KW_noreset
>     | SV_KW_valueof
>     | SV_KW_valueOf
>     | SV_KW_stringof
>     | SV_KW_stringOf
>     | SV_KW_clocked_by
>     | SV_KW_reset_by
>     | SV_KW_powered_by
>     | SV_KW_Action
>     | SV_KW_ActionValue
>       deriving (Show, Eq, Ord, Enum, Bounded)


Symbols

> data SV_Symbol
>     = SV_SYM_plus
>     | SV_SYM_minus
>     | SV_SYM_bang
>     | SV_SYM_tilde
>     | SV_SYM_et
>     | SV_SYM_tilde_et
>     | SV_SYM_pipe
>     | SV_SYM_tilde_pipe
>     | SV_SYM_caret
>     | SV_SYM_tilde_caret
>     | SV_SYM_caret_tilde
>     | SV_SYM_star
>     | SV_SYM_slash
>     | SV_SYM_percent
>     | SV_SYM_eq_eq
>     | SV_SYM_bang_eq
>     | SV_SYM_eq_eq_eq
>     | SV_SYM_bang_eq_eq
>     | SV_SYM_eq_question_eq
>     | SV_SYM_bang_question_eq
>     | SV_SYM_et_et
>     | SV_SYM_pipe_pipe
>     | SV_SYM_star_star
>     | SV_SYM_lt
>     | SV_SYM_lt_eq
>     | SV_SYM_gt
>     | SV_SYM_gt_eq
>     | SV_SYM_gt_gt
>     | SV_SYM_lt_lt
>     | SV_SYM_gt_gt_gt
>     | SV_SYM_lt_lt_lt
>     | SV_SYM_plus_plus
>     | SV_SYM_minus_minus
>     | SV_SYM_colon_colon
>     | SV_SYM_colon
>     | SV_SYM_dot
>     | SV_SYM_eq
>     | SV_SYM_plus_eq
>     | SV_SYM_minus_eq
>     | SV_SYM_tick
>     | SV_SYM_backtick
>     | SV_SYM_comma
>     | SV_SYM_semi
>     | SV_SYM_lparen
>     | SV_SYM_rparen
>     | SV_SYM_lparen_star
>     | SV_SYM_star_rparen
>     | SV_SYM_lbracket
>     | SV_SYM_rbracket
>     | SV_SYM_lbrace
>     | SV_SYM_rbrace
>     | SV_SYM_question
>     | SV_SYM_hash
>       -- Assertion symbols
>     | SV_SYM_hash_hash
>     | SV_SYM_dollar
>     | SV_SYM_pipe_eq_gt
>     | SV_SYM_pipe_minus_gt
>     | SV_SYM_minus_gt
>     | SV_SYM_lbracket_star
>     | SV_SYM_lbracket_minus_gt
>     | SV_SYM_lbracket_eq
>       -- Assignment Shortcuts
>     | SV_SYM_pipe_eq
>     | SV_SYM_caret_eq
>     | SV_SYM_percent_eq
>     | SV_SYM_et_eq
>     | SV_SYM_slash_eq
>     | SV_SYM_lt_lt_eq
>     | SV_SYM_gt_gt_eq
>     | SV_SYM_lt_lt_lt_eq
>     | SV_SYM_gt_gt_gt_eq
>       -- Bluespec symbols
>     | SV_SYM_dot_star
>     | SV_SYM_lt_minus
>     | SV_SYM_lt_gt
>     | SV_SYM_dot_dot
>     | SV_SYM_et_et_et -- temporary for patterns
>       deriving (Show, Eq, Ord, Enum, Bounded)

Keyword table, in machine readable form.  Used to generate a keyword
scanner and to prettyprint keywords.

> svKeywordTable :: [(SV_Keyword, String, SV_Version)]
> svKeywordTable =
>     [(SV_KW_alias,               "alias",                SystemVerilog31),
>      (SV_KW_always,              "always",               Verilog2001),
>      (SV_KW_always_comb,         "always_comb",          SystemVerilog30),
>      (SV_KW_always_ff,           "always_ff",            SystemVerilog30),
>      (SV_KW_always_latch,        "always_latch",         SystemVerilog30),
>      (SV_KW_and,                 "and",                  Verilog2001),
>      (SV_KW_assert,              "assert",               SystemVerilog30),
>      (SV_KW_assert_strobe,       "assert_strobe",        SystemVerilog30),
>      (SV_KW_assign,              "assign",               Verilog2001),
>      (SV_KW_assume,              "assume",               SystemVerilog31a),
>      (SV_KW_automatic,           "automatic",            Verilog2001),
>      (SV_KW_before,              "before",               SystemVerilog31),
>      (SV_KW_begin,               "begin",                Verilog2001),
>      (SV_KW_bind,                "bind",                 SystemVerilog31),
>      (SV_KW_bins,                "bins",                 SystemVerilog31a),
>      (SV_KW_binsof,              "binsof",               SystemVerilog31a),
>      (SV_KW_bit,                 "bit",                  SystemVerilog30),
>      (SV_KW_break,               "break",                SystemVerilog30),
>      (SV_KW_buf,                 "buf",                  Verilog2001),
>      (SV_KW_bufif0,              "bufif0",               Verilog2001),
>      (SV_KW_bufif1,              "bufif1",               Verilog2001),
>      (SV_KW_byte,                "byte",                 SystemVerilog30),
>      (SV_KW_case,                "case",                 Verilog2001),
>      (SV_KW_casex,               "casex",                Verilog2001),
>      (SV_KW_casez,               "casez",                Verilog2001),
>      (SV_KW_cell,                "cell",                 Verilog2001),
>      (SV_KW_chandle,             "chandle",              SystemVerilog31),
>      (SV_KW_class,               "class",                SystemVerilog31),
>      (SV_KW_clocking,            "clocking",             SystemVerilog31),
>      (SV_KW_cmos,                "cmos",                 Verilog2001),
>      (SV_KW_config,              "config",               Verilog2001),
>      (SV_KW_const,               "const",                SystemVerilog30),
>      (SV_KW_constraint,          "constraint",           SystemVerilog31),
>      (SV_KW_context,             "context",              SystemVerilog31),
>      (SV_KW_continue,            "continue",             SystemVerilog30),
>      (SV_KW_cover,               "cover",                SystemVerilog31),
>      (SV_KW_covergroup,          "covergroup",           SystemVerilog31a),
>      (SV_KW_coverpoint,          "coverpoint",           SystemVerilog31a),
>      (SV_KW_cross,               "cross",                SystemVerilog31),
>      (SV_KW_deassign,            "deassign",             Verilog2001),
>      (SV_KW_default,             "default",              Verilog2001),
>      (SV_KW_defparam,            "defparam",             Verilog2001),
>      (SV_KW_design,              "design",               Verilog2001),
>      (SV_KW_disable,             "disable",              Verilog2001),
>      (SV_KW_dist,                "dist",                 SystemVerilog31),
>      (SV_KW_do,                  "do",                   SystemVerilog30),
>      (SV_KW_edge,                "edge",                 Verilog2001),
>      (SV_KW_else,                "else",                 Verilog2001),
>      (SV_KW_end,                 "end",                  Verilog2001),
>      (SV_KW_endcase,             "endcase",              Verilog2001),
>      (SV_KW_endclass,            "endclass",             SystemVerilog31),
>      (SV_KW_endclocking,         "endclocking",          SystemVerilog31),
>      (SV_KW_endconfig,           "endconfig",            Verilog2001),
>      (SV_KW_endfunction,         "endfunction",          Verilog2001),
>      (SV_KW_endgenerate,         "endgenerate",          Verilog2001),
>      (SV_KW_endgroup,            "endgroup",             SystemVerilog31a),
>      (SV_KW_endinterface,        "endinterface",         SystemVerilog30),
>      (SV_KW_endmodule,           "endmodule",            Verilog2001),
>      (SV_KW_endpackage,          "endpackage",           SystemVerilog31a),
>      (SV_KW_endprimitive,        "endprimitive",         Verilog2001),
>      (SV_KW_endprogram,          "endprogram",           SystemVerilog31),
>      (SV_KW_endproperty,         "endproperty",          SystemVerilog31),
>      (SV_KW_endspecify,          "endspecify",           Verilog2001),
>      (SV_KW_endsequence,         "endsequence",          SystemVerilog31),
>      (SV_KW_endtable,            "endtable",             Verilog2001),
>      (SV_KW_endtask,             "endtask",              Verilog2001),
>      (SV_KW_enum,                "enum",                 SystemVerilog30),
>      (SV_KW_event,               "event",                Verilog2001),
>      (SV_KW_expect,              "expect",               SystemVerilog31a),
>      (SV_KW_export,              "export",               SystemVerilog30),
>      (SV_KW_extends,             "extends",              SystemVerilog31),
>      (SV_KW_extern,              "extern",               SystemVerilog30),
>      (SV_KW_final,               "final",                SystemVerilog31),
>      (SV_KW_first_match,         "first_match",          SystemVerilog31),
>      (SV_KW_for,                 "for",                  Verilog2001),
>      (SV_KW_force,               "force",                Verilog2001),
>      (SV_KW_foreach,             "foreach",              SystemVerilog31a),
>      (SV_KW_forever,             "forever",              Verilog2001),
>      (SV_KW_fork,                "fork",                 Verilog2001),
>      (SV_KW_forkjoin,            "forkjoin",             SystemVerilog30),
>      (SV_KW_function,            "function",             Verilog2001),
>      (SV_KW_generate,            "generate",             Verilog2001),
>      (SV_KW_genvar,              "genvar",               Verilog2001),
>      (SV_KW_highz0,              "highz0",               Verilog2001),
>      (SV_KW_highz1,              "highz1",               Verilog2001),
>      (SV_KW_if,                  "if",                   Verilog2001),
>      (SV_KW_iff,                 "iff",                  SystemVerilog30),
>      (SV_KW_ifnone,              "ifnone",               Verilog2001),
>      (SV_KW_ignore_bins,         "ignore_bins",          SystemVerilog31a),
>      (SV_KW_illegal_bins,        "illegal_bins",         SystemVerilog31a),
>      (SV_KW_import,              "import",               SystemVerilog30),
>      (SV_KW_incdir,              "incdir",               Verilog2001),
>      (SV_KW_include,             "include",              Verilog2001),
>      (SV_KW_initial,             "initial",              Verilog2001),
>      (SV_KW_inout,               "inout",                Verilog2001),
>      (SV_KW_input,               "input",                Verilog2001),
>      (SV_KW_inside,              "inside",               SystemVerilog31),
>      (SV_KW_instance,            "instance",             Verilog2001),
>      (SV_KW_int,                 "int",                  SystemVerilog30),
>      (SV_KW_integer,             "integer",              Verilog2001),
>      (SV_KW_interface,           "interface",            SystemVerilog30),
>      (SV_KW_intersect,           "intersect",            SystemVerilog31),
>      (SV_KW_join,                "join",                 Verilog2001),
>      (SV_KW_join_any,            "join_any",             SystemVerilog31),
>      (SV_KW_join_none,           "join_none",            SystemVerilog31),
>      (SV_KW_large,               "large",                Verilog2001),
>      (SV_KW_liblist,             "liblist",              Verilog2001),
>      (SV_KW_library,             "library",              Verilog2001),
>      (SV_KW_local,               "local",                SystemVerilog31),
>      (SV_KW_localparam,          "localparam",           Verilog2001),
>      (SV_KW_logic,               "logic",                SystemVerilog30),
>      (SV_KW_longint,             "longint",              SystemVerilog30),
>      (SV_KW_macromodule,         "macromodule",          Verilog2001),
>      (SV_KW_matches,             "matches",              SystemVerilog31a),
>      (SV_KW_medium,              "medium",               Verilog2001),
>      (SV_KW_modport,             "modport",              SystemVerilog30),
>      (SV_KW_module,              "module",               Verilog2001),
>      (SV_KW_nand,                "nand",                 Verilog2001),
>      (SV_KW_negedge,             "negedge",              Verilog2001),
>      (SV_KW_new,                 "new",                  SystemVerilog31),
>      (SV_KW_nmos,                "nmos",                 Verilog2001),
>      (SV_KW_nor,                 "nor",                  Verilog2001),
>      (SV_KW_noshowcancelled,     "noshowcancelled",      Verilog2001),
>      (SV_KW_not,                 "not",                  Verilog2001),
>      (SV_KW_notif0,              "notif0",               Verilog2001),
>      (SV_KW_notif1,              "notif1",               Verilog2001),
>      (SV_KW_null,                "null",                 SystemVerilog31),
>      (SV_KW_or,                  "or",                   Verilog2001),
>      (SV_KW_output,              "output",               Verilog2001),
>      (SV_KW_package,             "package",              SystemVerilog31a),
>      (SV_KW_packed,              "packed",               SystemVerilog30),
>      (SV_KW_parameter,           "parameter",            Verilog2001),
>      (SV_KW_pmos,                "pmos",                 Verilog2001),
>      (SV_KW_posedge,             "posedge",              Verilog2001),
>      (SV_KW_primitive,           "primitive",            Verilog2001),
>      (SV_KW_priority,            "priority",             SystemVerilog30),
>      (SV_KW_program,             "program",              SystemVerilog31),
>      (SV_KW_property,            "property",             SystemVerilog31),
>      (SV_KW_protected,           "protected",            SystemVerilog31),
>      (SV_KW_pull0,               "pull0",                Verilog2001),
>      (SV_KW_pull1,               "pull1",                Verilog2001),
>      (SV_KW_pulldown,            "pulldown",             Verilog2001),
>      (SV_KW_pullup,              "pullup",               Verilog2001),
>      (SV_KW_pulsestyle_onevent,  "pulsestyle_onevent",   Verilog2001),
>      (SV_KW_pulsestyle_ondetect, "pulsestyle_ondetect",  Verilog2001),
>      (SV_KW_pure,                "pure",                 SystemVerilog31),
>      (SV_KW_rand,                "rand",                 SystemVerilog31),
>      (SV_KW_randc,               "randc",                SystemVerilog31),
>      (SV_KW_randcase,            "randcase",             SystemVerilog31a),
>      (SV_KW_randsequence,        "randsequence",         SystemVerilog31a),
>      (SV_KW_rcmos,               "rcmos",                Verilog2001),
>      (SV_KW_real,                "real",                 Verilog2001),
>      (SV_KW_realtime,            "realtime",             Verilog2001),
>      (SV_KW_ref,                 "ref",                  SystemVerilog31),
>      (SV_KW_reg,                 "reg",                  Verilog2001),
>      (SV_KW_release,             "release",              Verilog2001),
>      (SV_KW_repeat,              "repeat",               Verilog2001),
>      (SV_KW_return,              "return",               SystemVerilog30),
>      (SV_KW_rnmos,               "rnmos",                Verilog2001),
>      (SV_KW_rpmos,               "rpmos",                Verilog2001),
>      (SV_KW_rtran,               "rtran",                Verilog2001),
>      (SV_KW_rtranif0,            "rtranif0",             Verilog2001),
>      (SV_KW_rtranif1,            "rtranif1",             Verilog2001),
>      (SV_KW_scalared,            "scalared",             Verilog2001),
>      (SV_KW_sequence,            "sequence",             SystemVerilog31),
>      (SV_KW_shortint,            "shortint",             SystemVerilog30),
>      (SV_KW_shortreal,           "shortreal",            SystemVerilog30),
>      (SV_KW_showcancelled,       "showcancelled",        Verilog2001),
>      (SV_KW_signed,              "signed",               Verilog2001),
>      (SV_KW_small,               "small",                Verilog2001),
>      (SV_KW_solve,               "solve",                SystemVerilog31),
>      (SV_KW_specify,             "specify",              Verilog2001),
>      (SV_KW_specparam,           "specparam",            Verilog2001),
>      (SV_KW_static,              "static",               SystemVerilog30),
>      (SV_KW_string,              "string",               SystemVerilog31),
>      (SV_KW_strong0,             "strong0",              Verilog2001),
>      (SV_KW_strong1,             "strong1",              Verilog2001),
>      (SV_KW_struct,              "struct",               SystemVerilog30),
>      (SV_KW_super,               "super",                SystemVerilog31),
>      (SV_KW_supply0,             "supply0",              Verilog2001),
>      (SV_KW_supply1,             "supply1",              Verilog2001),
>      (SV_KW_table,               "table",                Verilog2001),
>      (SV_KW_tagged,              "tagged",               SystemVerilog31a),
>      (SV_KW_task,                "task",                 Verilog2001),
>      (SV_KW_this,                "this",                 SystemVerilog31),
>      (SV_KW_throughout,          "throughout",           SystemVerilog31),
>      (SV_KW_time,                "time",                 Verilog2001),
>      (SV_KW_timeprecision,       "timeprecision",        Verilog2001),
>      (SV_KW_timeunit,            "timeunit",             SystemVerilog30),
>      (SV_KW_tran,                "tran",                 Verilog2001),
>      (SV_KW_tranif0,             "tranif0",              Verilog2001),
>      (SV_KW_tranif1,             "tranif1",              Verilog2001),
>      (SV_KW_tri,                 "tri",                  Verilog2001),
>      (SV_KW_tri0,                "tri0",                 Verilog2001),
>      (SV_KW_tri1,                "tri1",                 Verilog2001),
>      (SV_KW_triand,              "triand",               Verilog2001),
>      (SV_KW_trior,               "trior",                Verilog2001),
>      (SV_KW_trireg,              "trireg",               Verilog2001),
>      (SV_KW_type,                "type",                 SystemVerilog30),
>      (SV_KW_typedef,             "typedef",              SystemVerilog30),
>      (SV_KW_union,               "union",                SystemVerilog30),
>      (SV_KW_unique,              "unique",               SystemVerilog30),
>      (SV_KW_unsigned,            "unsigned",             Verilog2001),
>      (SV_KW_use,                 "use",                  Verilog2001),
>      (SV_KW_var,                 "var",                  SystemVerilog31),
>      (SV_KW_vectored,            "vectored",             Verilog2001),
>      (SV_KW_virtual,             "virtual",              SystemVerilog31),
>      (SV_KW_void,                "void",                 SystemVerilog30),
>      (SV_KW_wait,                "wait",                 Verilog2001),
>      (SV_KW_wait_order,          "wait_order",           SystemVerilog31),
>      (SV_KW_wand,                "wand",                 Verilog2001),
>      (SV_KW_weak0,               "weak0",                Verilog2001),
>      (SV_KW_weak1,               "weak1",                Verilog2001),
>      (SV_KW_while,               "while",                Verilog2001),
>      (SV_KW_wildcard,            "wildcard",             SystemVerilog31a),
>      (SV_KW_wire,                "wire",                 Verilog2001),
>      (SV_KW_with,                "with",                 SystemVerilog31),
>      (SV_KW_within,              "within",               SystemVerilog31),
>      (SV_KW_wor,                 "wor",                  Verilog2001),
>      (SV_KW_xnor,                "xnor",                 Verilog2001),
>      (SV_KW_xor,                 "xor",                  Verilog2001),
>      -- Bluespec 3.8 keywords
>      (SV_KW_action,              "action",               Bluespec38),
>      (SV_KW_endaction,           "endaction",            Bluespec38),
>      (SV_KW_actionvalue,         "actionvalue",          Bluespec38),
>      (SV_KW_endactionvalue,      "endactionvalue",       Bluespec38),
>      (SV_KW_deriving,            "deriving",             Bluespec38),
>      (SV_KW_endinstance,         "endinstance",          Bluespec38),
>      (SV_KW_let,                 "let",                  Bluespec38),
>      (SV_KW_match,               "match",                Bluespec38),
>      (SV_KW_method,              "method",               Bluespec38),
>      (SV_KW_endmethod,           "endmethod",            Bluespec38),
>      (SV_KW_par,                 "par",                  Bluespec38),
>      (SV_KW_endpar,              "endpar",               Bluespec38),
>      (SV_KW_abortif,             "abortif",              Bluespec38),
>      (SV_KW_provisos,            "provisos",             Bluespec38),
>      (SV_KW_rule,                "rule",                 Bluespec38),
>      (SV_KW_endrule,             "endrule",              Bluespec38),
>      (SV_KW_rules,               "rules",                Bluespec38),
>      (SV_KW_endrules,            "endrules",             Bluespec38),
>      (SV_KW_seq,                 "seq",                  Bluespec38),
>      (SV_KW_endseq,              "endseq",               Bluespec38),
>      (SV_KW_goto,                "goto",                 Bluespec38),
>--      (SV_KW_schedule,            "schedule",             Bluespec38),
>      (SV_KW_typeclass,           "typeclass",            Bluespec38),
>      (SV_KW_endtypeclass,        "endtypeclass",         Bluespec38),
>--      (SV_KW_clock,               "clock",                Bluespec38),
>--      (SV_KW_reset,               "reset",                Bluespec38),
>--      (SV_KW_noreset,             "noreset",              Bluespec38),
>      (SV_KW_valueof,             "valueof",              Bluespec38),
>      (SV_KW_valueOf,             "valueOf",              Bluespec38),
>      (SV_KW_stringof,            "stringof",             Bluespec38), -- XXX should these be "Bluespec38"?
>      (SV_KW_stringOf,            "stringOf",             Bluespec38),
>      (SV_KW_clocked_by,           "clocked_by",            Bluespec38),
>      (SV_KW_reset_by,             "reset_by",              Bluespec38),
>      (SV_KW_powered_by,           "powered_by",            Bluespec38),
>      (SV_KW_Action,              "Action",               Bluespec38),
>      (SV_KW_ActionValue,         "ActionValue",          Bluespec38)]

Symbol table

> svSymbolTable :: [(SV_Symbol, String, SV_Version)]
> svSymbolTable =
>     [(SV_SYM_plus,                "+",                    Verilog2001),
>      (SV_SYM_minus,               "-",                    Verilog2001),
>      (SV_SYM_bang,                "!",                    Verilog2001),
>      (SV_SYM_tilde,               "~",                    Verilog2001),
>      (SV_SYM_et,                  "&",                    Verilog2001),
>      (SV_SYM_tilde_et,            "~&",                   Verilog2001),
>      (SV_SYM_pipe,                "|",                    Verilog2001),
>      (SV_SYM_tilde_pipe,          "~|",                   Verilog2001),
>      (SV_SYM_caret,               "^",                    Verilog2001),
>      (SV_SYM_tilde_caret,         "~^",                   Verilog2001),
>      (SV_SYM_caret_tilde,         "^~",                   Verilog2001),
>      (SV_SYM_star,                "*",                    Verilog2001),
>      (SV_SYM_slash,               "/",                    Verilog2001),
>      (SV_SYM_percent,             "%",                    Verilog2001),
>      (SV_SYM_eq_eq,               "==",                   Verilog2001),
>      (SV_SYM_bang_eq,             "!=",                   Verilog2001),
>      (SV_SYM_eq_eq_eq,            "===",                  Verilog2001),
>      (SV_SYM_bang_eq_eq,          "!==",                  Verilog2001),
>      (SV_SYM_eq_question_eq,      "=?=",                  SystemVerilog31),
>      (SV_SYM_bang_question_eq,    "!?=",                  SystemVerilog31),
>      (SV_SYM_et_et,               "&&",                   Verilog2001),
>      (SV_SYM_pipe_pipe,           "||",                   Verilog2001),
>      (SV_SYM_star_star,           "**",                   Verilog2001),
>      (SV_SYM_lt,                  "<",                    Verilog2001),
>      (SV_SYM_lt_eq,               "<=",                   Verilog2001),
>      (SV_SYM_gt,                  ">",                    Verilog2001),
>      (SV_SYM_gt_eq,               ">=",                   Verilog2001),
>      (SV_SYM_gt_gt,               ">>",                   Verilog2001),
>      (SV_SYM_lt_lt,               "<<",                   Verilog2001),
>      (SV_SYM_gt_gt_gt,            ">>>",                  Verilog2001),
>      (SV_SYM_lt_lt_lt,            "<<<",                  Verilog2001),
>      (SV_SYM_plus_plus,           "++",                   SystemVerilog30),
>      (SV_SYM_minus_minus,         "--",                   SystemVerilog30),
>      (SV_SYM_tick,                "'",                    Verilog2001),
>      (SV_SYM_backtick,            "`",                    Verilog2001),
>      (SV_SYM_colon_colon,         "::",           {- ? -} SystemVerilog30),
>      (SV_SYM_colon,               ":",                    Verilog2001),
>      (SV_SYM_dot,                 ".",                    Verilog2001),
>      (SV_SYM_eq,                  "=",                    Verilog2001),
>      (SV_SYM_plus_eq,             "+=",           {- ? -} Verilog2001),
>      (SV_SYM_minus_eq,            "-=",           {- ? -} Verilog2001),
>      (SV_SYM_comma,               ",",                    Verilog2001),
>      (SV_SYM_semi,                ";",                    Verilog2001),
>      (SV_SYM_lparen,              "(",                    Verilog2001),
>      (SV_SYM_rparen,              ")",                    Verilog2001),
>      (SV_SYM_lparen_star,         "(*",                   Verilog2001),
>      (SV_SYM_star_rparen,         "*)",                   Verilog2001),
>      (SV_SYM_lbracket,            "[",                    Verilog2001),
>      (SV_SYM_rbracket,            "]",                    Verilog2001),
>      (SV_SYM_lbrace,              "{",                    Verilog2001),
>      (SV_SYM_rbrace,              "}",                    Verilog2001),
>      (SV_SYM_question,            "?",                    Verilog2001),
>      (SV_SYM_hash,                "#",            {- ? -} Verilog2001),
>      (SV_SYM_hash_hash,           "##",  {- Assertions -} SystemVerilog31a),
>      (SV_SYM_dollar,              "$",                    SystemVerilog31a),
>      (SV_SYM_pipe_eq_gt,          "|=>",                  SystemVerilog31a),
>      (SV_SYM_pipe_minus_gt,       "|->",                  SystemVerilog31a),
>      (SV_SYM_minus_gt,            "->",                   SystemVerilog31a),
>      (SV_SYM_lbracket_star,        "[*",                  SystemVerilog31a),
>      (SV_SYM_lbracket_minus_gt,    "[->",                 SystemVerilog31a),
>      (SV_SYM_lbracket_eq,          "[=",                  SystemVerilog31a),
>      (SV_SYM_pipe_eq,             "|=", {- Assigns -}     SystemVerilog31a),
>      (SV_SYM_caret_eq,            "^=",                   SystemVerilog31a),
>      (SV_SYM_percent_eq,          "%=",                   SystemVerilog31a),
>      (SV_SYM_et_eq,               "&=",                   SystemVerilog31a),
>      (SV_SYM_slash_eq,            "/=",                   SystemVerilog31a),
>      (SV_SYM_lt_lt_eq,            "<<=",                  SystemVerilog31a),
>      (SV_SYM_gt_gt_eq,            ">>=",                  SystemVerilog31a),
>      (SV_SYM_lt_lt_lt_eq,         "<<<=",                 SystemVerilog31a),
>      (SV_SYM_gt_gt_gt_eq,         ">>>=",                 SystemVerilog31a),
>      (SV_SYM_dot_star,            ".*",                   Bluespec38),
>      (SV_SYM_lt_minus,            "<-",                   Bluespec38),
>      (SV_SYM_lt_gt,               "<>",                   Bluespec38),
>      (SV_SYM_dot_dot,             "..",                   Bluespec38),
>      (SV_SYM_et_et_et,            "&&&",                  Bluespec38)]

Unique characters that are elements of symbols

> svSymbolChars :: [Char]
> svSymbolChars = nub (concat [s | (_, s, _) <- svSymbolTable])

SELF-TEST

Check that a given table contains each keyword uniquely
Returns () if symbol table is okay; quits with an error otherwise

> checkTable :: (Show a, Bounded a, Enum a, Ord a) =>
>               [(a, String, SV_Version)] -> IO ()
> checkTable table =
>     do let itemsInTable = sort [item | (item, _, _) <- table]
>            duplicateItems = [item | (item:_:_) <- group itemsInTable]
>            unhandledItems = [minBound .. maxBound] \\ itemsInTable
>            display item = "    " ++ show item
>        when (not (null unhandledItems))
>             (do hPutStrLn stderr "ERROR: missing entries in table:"
>                 mapM_ (putStrLn . display) unhandledItems)
>        when (not (null duplicateItems))
>             (do hPutStrLn stderr "ERROR: duplicate entries in table:"
>                 mapM_ (putStrLn . display) duplicateItems)
>        when (not (null unhandledItems && null duplicateItems))
>             (exitWith (ExitFailure 1))

Self-test of this module

> checkSystemVerilogKeywords :: IO ()
> checkSystemVerilogKeywords =
>     do checkTable svKeywordTable
>        checkTable svSymbolTable
