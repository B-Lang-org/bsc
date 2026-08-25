/**
 * @file The Bluespec hardware design language (classic syntax)
 * @author Mieszko
 * @license MIT
 */

/// <reference types="tree-sitter-cli/dsl" />
// @ts-check

const PREC = {
  SIGNATURE: 1,
  CLAUSE: 2,
  WHERE: 3,
  INFIX: 4,
  LAMBDA: 5,
  IF: 6,
  DO: 7,
  APPLY: 10,
  SELECT: 11,
};

function sep1(delimiter, rule) {
  return seq(rule, repeat(seq(delimiter, rule)));
}

function layout_body($, item) {
  return seq(item, repeat(seq($._separator, item)), optional($._separator));
}

export default grammar({
  name: "bluespec",

  externals: $ => [
    $._layout_open_brace,
    $._layout_close_brace,
    $._layout_semicolon,
    $._empty_layout,
    $.comment,
    $.pragma,
    $._cpp_line,
    $._interface_layout_open,
  ],

  extras: $ => [
    /\s/,
    $.comment,
    $.pragma,
    $._cpp_line,
  ],

  word: $ => $._varid,

  conflicts: $ => [
    [$.class_definition, $._atype],
    [$.class_constraint, $.type_constructor],
    [$._lexp, $._module_stmt],
    [$.interface_expression, $.module_interface],
    [$._aexp, $._apat],
    [$.unit_expression, $.unit_pattern],
    [$.list_expression, $.list_pattern],
    [$.class_constraint, $.instance_definition],
    [$.bind_statement, $._apat],
  ],

  supertypes: $ => [
    $._definition,
    $._literal,
  ],

  rules: {
    source_file: $ => choice(
      $.package_definition,
      seq(optional($._package_body_inner)),
    ),

    package_definition: $ => seq(
      'package',
      field('name', $.module_identifier),
      optional($.export_list),
      'where',
      $._package_body,
    ),

    module_identifier: $ => choice($._conid, $._varid),

    export_list: $ => choice(
      seq(
        '(',
        optional(sep1(',', $.export)),
        optional(','),
        ')',
      ),
      seq(
        'hiding',
        '(',
        optional(sep1(',', $.export)),
        ')',
      ),
    ),

    export: $ => choice(
      seq($.constructor_identifier, '(', '..', ')'),
      seq($.constructor_identifier, '(', optional(sep1(',', choice($.variable_identifier, $.constructor_identifier, $._varsym, $._consym))), ')'),
      $.constructor_identifier,
      $.variable_identifier,
      seq('package', $.module_identifier),
      seq('(', $._varsym, ')'),
      seq('(', $._consym, ')'),
      $._varsym,
      $._consym,
      $._system_task_id,
    ),

    _package_body: $ => choice(
      seq('{', optional($._package_body_inner), '}'),
      seq($._layout_open_brace, optional($._package_body_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _package_body_inner: $ => layout_body($, $._top_declaration),

    _separator: $ => seq(choice(';', $._layout_semicolon), repeat(';')),

    _top_declaration: $ => choice(
      $.import_declaration,
      $.fixity_declaration,
      $._definition,
    ),

    import_declaration: $ => seq(
      'import',
      optional('qualified'),
      field('module', $.module_identifier),
    ),

    fixity_declaration: $ => seq(
      field('fixity', choice('infixl', 'infixr', 'infix')),
      field('precedence', $.integer_literal),
      sep1(',', field('operator', choice(
        $._varsym,
        $._consym,
        $.variable_identifier,
        $.constructor_identifier,
        seq('`', choice($.variable_identifier, $.constructor_identifier), '`'),
      ))),
    ),

    _definition: $ => choice(
      $.type_definition,
      $.data_definition,
      $.struct_definition,
      $.class_definition,
      $.instance_definition,
      $.type_signature,
      $.function_definition,
      $.foreign_declaration,
      $.primitive_declaration,
    ),

    type_definition: $ => seq(
      'type',
      field('name', choice(
        $.constructor_identifier,
        seq('(', $.constructor_identifier, '::', $._type, ')'),
      )),
      repeat($.type_variable),
      '=',
      field('type', $._type),
    ),

    data_definition: $ => seq(
      'data',
      field('name', choice(
        $.constructor_identifier,
        seq('(', $.constructor_identifier, '::', $._type, ')'),
      )),
      repeat($.type_variable),
      optional(seq(
        '=',
        sep1('|', $.data_constructor),
      )),
      optional($.deriving_clause),
    ),

    data_constructor: $ => seq(
      field('name', choice(
        $.constructor_identifier,
        seq('(', sep1(',', $.constructor_identifier), ')'),
      )),
      repeat($._atype),
      optional(seq('{', sep1(choice(';', $._layout_semicolon), $.field_declaration), optional(choice(';', $._layout_semicolon)), '}')),
    ),

    field_declaration: $ => seq(
      field('name', $.variable_identifier),
      '::',
      field('type', $.qualified_type),
    ),

    deriving_clause: $ => seq(
      'deriving',
      '(',
      sep1(',', $.constructor_identifier),
      ')',
    ),

    struct_definition: $ => seq(
      choice('struct', 'interface'),
      field('name', choice(
        $.constructor_identifier,
        seq('(', $.constructor_identifier, '::', $._type, ')'),
      )),
      repeat($.type_variable),
      '=',
      $._struct_body,
      optional($.deriving_clause),
    ),

    _struct_body: $ => choice(
      seq('{', optional(seq(sep1(choice(';', $._layout_semicolon), $.struct_field), optional(choice(';', $._layout_semicolon)))), '}'),
      seq($._layout_open_brace, optional(seq(sep1(choice(';', $._layout_semicolon), $.struct_field), optional(choice(';', $._layout_semicolon)))), $._layout_close_brace),
    ),

    struct_field: $ => seq(
      field('name', $.variable_identifier),
      '::',
      field('type', $.qualified_type),
    ),

    class_definition: $ => seq(
      'class',
      optional(choice('coherent', 'incoherent')),
      optional(seq('(', $.constructor_identifier, '::', $._type, ')')),
      optional($.class_context),
      field('name', $.constructor_identifier),
      repeat($.type_variable),
      optional($.functional_dependencies),
      optional(seq(
        'where',
        $._class_body,
      )),
    ),

    class_context: $ => seq(
      choice(
        $.class_constraint,
        seq('(', sep1(',', $.class_constraint), ')'),
      ),
      '=>',
    ),

    class_constraint: $ => seq(
      $.constructor_identifier,
      repeat($._atype),
    ),

    functional_dependencies: $ => seq(
      '|',
      sep1(',', $.functional_dependency),
    ),

    functional_dependency: $ => seq(
      repeat1($.type_variable),
      '->',
      repeat1($.type_variable),
    ),

    _class_body: $ => choice(
      seq('{', optional($._class_body_inner), '}'),
      seq($._layout_open_brace, optional($._class_body_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _class_body_inner: $ => layout_body($, $._class_member),

    _class_member: $ => choice(
      $.type_signature,
      $.function_definition,
    ),

    instance_definition: $ => seq(
      'instance',
      optional($.class_context),
      choice(
        seq(field('class', $.constructor_identifier), repeat($._atype)),
        seq('(', field('class', $.constructor_identifier), repeat($._atype), ')'),
      ),
      optional(seq(
        'where',
        $._instance_body,
      )),
    ),

    _instance_body: $ => choice(
      seq('{', optional($._instance_body_inner), '}'),
      seq($._layout_open_brace, optional($._instance_body_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _instance_body_inner: $ => layout_body($, $._instance_member),

    _instance_member: $ => choice(
      $.function_definition,
      $.type_signature,
    ),

    type_signature: $ => prec(PREC.SIGNATURE, seq(
      field('name', choice(
        $.variable_identifier,
        seq('(', $.operator, ')'),
        $._system_task_id,
      )),
      '::',
      field('type', $.qualified_type),
    )),

    qualified_type: $ => seq(
      optional($.class_context),
      $._type,
    ),

    function_definition: $ => prec(PREC.CLAUSE, seq(
      field('name', choice(
        $.variable_identifier,
        seq('(', $.operator, ')'),
        seq($._apat, $.operator, $._apat),
        $.wildcard,
        $._system_task_id,
      )),
      repeat($._apat),
      optional(seq('::', field('type', $.qualified_type))),
      optional($.guard),
      $._rhs,
    )),

    _rhs: $ => seq(
      '=',
      field('body', $._expression),
      optional($.where_clause),
    ),

    guard: $ => choice(
      seq('|', sep1(',', $._expression)),
      seq('when', sep1(',', $._expression)),
    ),

    where_clause: $ => seq(
      'where',
      $._where_body,
    ),

    _where_body: $ => choice(
      seq('{', optional($._where_body_inner), '}'),
      seq($._layout_open_brace, optional($._where_body_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _where_body_inner: $ => layout_body($, $._where_binding),

    _where_binding: $ => choice(
      $.type_signature,
      $.function_definition,
      $.pattern_binding,
    ),

    pattern_binding: $ => seq(
      field('pattern', $._pattern),
      '=',
      field('body', $._expression),
      optional($.where_clause),
    ),

    foreign_declaration: $ => seq(
      'foreign',
      field('name', choice($.variable_identifier, $._system_task_id)),
      '::',
      field('type', $.qualified_type),
      optional(seq('=', $.string_literal, optional(seq(',', '(', sep1(',', $.string_literal), ')')))),
    ),

    primitive_declaration: $ => seq(
      'primitive',
      choice(
        seq(
          field('name', $.variable_identifier),
          '::',
          field('type', $.qualified_type),
        ),
        seq(
          'type',
          field('name', $.constructor_identifier),
          optional(seq('::', $.qualified_type)),
        ),
      ),
    ),

    _type: $ => choice(
      $.function_type,
      $._btype,
    ),

    function_type: $ => prec.right(1, seq(
      field('parameter', $._btype),
      '->',
      field('return', $._type),
    )),

    _btype: $ => choice(
      $.type_application,
      $._atype,
    ),

    type_application: $ => prec.left(PREC.APPLY, seq(
      $._btype,
      $._atype,
    )),

    _atype: $ => choice(
      $.type_constructor,
      $.type_variable,
      $.type_literal,
      $.type_string_literal,
      $.type_tuple,
      $.type_unit,
      $.type_list,
      $.type_hash,
      $.kind_star,
      $.kind_hash,
      $.kind_string,
      seq('(', $._type, ')'),
    ),

    type_constructor: $ => $.constructor_identifier,
    type_variable: $ => $.variable_identifier,
    type_literal: $ => $.integer_literal,
    type_string_literal: $ => $.string_literal,

    kind_star: $ => prec(1, '*'),
    kind_hash: $ => prec(1, '#'),
    kind_string: $ => prec(1, '$'),

    type_tuple: $ => seq('(', $._type, ',', sep1(',', $._type), ')'),
    type_unit: $ => seq('(', ')'),
    type_list: $ => seq('[', $._type, ']'),
    type_hash: $ => seq('#', '(', sep1(',', $._type), ')'),

    _expression: $ => choice(
      $.where_expression,
      $._exp_infix,
    ),

    where_expression: $ => prec.right(PREC.WHERE, seq(
      $._exp_infix,
      $.where_clause,
    )),

    _exp_infix: $ => choice(
      $.infix_expression,
      $._lexp,
    ),

    infix_expression: $ => prec.left(PREC.INFIX, seq(
      $._exp_infix,
      $.operator,
      $._exp_infix,
    )),

    operator: $ => choice(
      $.variable_symbol,
      $.constructor_symbol,
      seq('`', choice($.variable_identifier, $.constructor_identifier), '`'),
    ),

    _lexp: $ => choice(
      $.lambda_expression,
      $.let_expression,
      $.letseq_expression,
      $.if_expression,
      $.case_expression,
      $.do_expression,
      $.action_expression,
      $.action_value_expression,
      $.braces_expression,
      $.module_expression,
      $.rules_expression,
      $.interface_expression,
      $.valueof_expression,
      $.stringof_expression,
      $.struct_expression,
      $.expression_type_signature,
      $._fexp,
    ),

    expression_type_signature: $ => prec(PREC.APPLY, seq(
      $._aexp,
      '::',
      $.qualified_type,
    )),

    lambda_expression: $ => prec.right(PREC.LAMBDA, seq(
      '\\',
      repeat1($._apat),
      '->',
      $._expression,
    )),

    let_expression: $ => prec.right(PREC.DO, seq(
      'let',
      $._let_bindings,
      'in',
      $._expression,
    )),

    letseq_expression: $ => prec.right(PREC.DO, seq(
      'letseq',
      $._let_bindings,
      'in',
      $._expression,
    )),

    _let_bindings: $ => choice(
      seq('{', optional($._let_bindings_inner), '}'),
      seq($._layout_open_brace, optional($._let_bindings_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _let_bindings_inner: $ => layout_body($, $._where_binding),

    if_expression: $ => prec.right(PREC.IF, seq(
      'if',
      field('condition', $._expression),
      'then',
      field('consequence', $._expression),
      'else',
      field('alternative', $._expression),
    )),

    case_expression: $ => seq(
      'case',
      field('scrutinee', $._expression),
      'of',
      $._case_body,
    ),

    _case_body: $ => choice(
      seq('{', optional($._case_alts_inner), '}'),
      seq($._layout_open_brace, optional($._case_alts_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _case_alts_inner: $ => layout_body($, $.case_alternative),

    case_alternative: $ => seq(
      field('pattern', $._pattern),
      optional(seq('when', sep1(',', $._qualifier))),
      '->',
      field('body', $._expression),
      optional($.where_clause),
    ),

    do_expression: $ => prec(PREC.DO, seq(
      'do',
      $._statement_block,
    )),

    action_expression: $ => prec(PREC.DO, seq(
      'action',
      $._statement_block,
    )),

    action_value_expression: $ => prec(PREC.DO, seq(
      'actionvalue',
      $._statement_block,
    )),

    module_expression: $ => prec(PREC.DO, choice(
      $.verilog_module,
      seq('module', $._module_body),
    )),

    braces_expression: $ => prec(PREC.DO, seq(
      '{', optional($._stmts_inner), '}',
    )),

    verilog_module: $ => prec.left(seq(
      'module', 'verilog', $._aexp, repeat(choice(seq(',', $._aexp), $._aexp)),
      '{', optional(seq(sep1(choice(';', $._layout_semicolon), $.verilog_port_binding), optional(choice(';', $._layout_semicolon)))), '}',
      optional($.verilog_schedule),
    )),

    verilog_schedule: $ => seq('[', sep1(',', $._expression), ']'),

    verilog_port_binding: $ => seq(
      $.variable_identifier,
      optional(seq('[', $.integer_literal, ']')),
      '=',
      repeat(choice($._aexp, $.port_attribute)),
    ),

    port_attribute: $ => seq($.string_literal, '{', $.variable_identifier, '}'),

    _module_body: $ => choice(
      seq('{', optional($._module_stmts_inner), '}'),
      seq($._layout_open_brace, optional($._module_stmts_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _module_stmts_inner: $ => layout_body($, $._module_stmt),

    _module_stmt: $ => choice(
      $.module_interface,
      $.rules_expression,
      $._statement,
    ),

    rules_expression: $ => prec(PREC.DO, seq(
      'rules',
      $._rules_body,
    )),

    _rules_body: $ => choice(
      seq('{', optional($._rules_inner), '}'),
      seq($._layout_open_brace, optional($._rules_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _rules_inner: $ => layout_body($, $.rule),

    rule: $ => seq(
      optional(seq(field('name', choice($.string_literal, $.parenthesized_expression, $.variable_identifier)), ':')),
      optional(seq(
        'when',
        sep1(',', $._qualifier),
      )),
      choice(
        seq('==>', field('body', $._expression)),
        field('body', $.rules_expression),
      ),
    ),

    _qualifier: $ => choice(
      $.pattern_guard,
      $._expression,
    ),

    pattern_guard: $ => prec.dynamic(1, seq(
      $._pattern,
      '<-',
      $._expression,
    )),

    interface_expression: $ => prec(PREC.DO, seq(
      'interface',
      $.constructor_identifier,
      $._interface_body,
    )),

    module_interface: $ => choice(
      prec(PREC.DO, seq('interface', '(', sep1(',', $._expression), ')')),
      prec(PREC.DO, seq('interface', $.constructor_identifier, $._interface_body)),
      prec(PREC.DO, seq('interface', $._module_interface_body)),
    ),

    _interface_body: $ => choice(
      seq('{', optional($._interface_bindings_inner), '}'),
      seq($._layout_open_brace, optional($._interface_bindings_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _module_interface_body: $ => choice(
      seq('{', optional($._interface_bindings_inner), '}'),
      seq($._interface_layout_open, optional($._interface_bindings_inner), $._layout_close_brace),
      $._empty_layout,
    ),

    _interface_bindings_inner: $ => layout_body($, $._interface_member),

    _interface_member: $ => choice(
      $.type_signature,
      $.interface_binding,
    ),

    interface_binding: $ => seq(
      field('name', $.variable_identifier),
      repeat($._apat),
      '=',
      field('body', $._expression),
      optional(seq('when', $._expression)),
    ),

    valueof_expression: $ => prec(1, choice(
      seq('valueOf', '(', $._type, ')'),
      seq('valueOf', $._atype),
    )),
    stringof_expression: $ => prec(1, choice(
      seq('stringOf', '(', $._type, ')'),
      seq('stringOf', $._atype),
    )),

    struct_expression: $ => prec(PREC.APPLY, seq(
      choice($.constructor_identifier, $._varid, $.wildcard, $.parenthesized_expression, $.field_selection),
      '{',
      optional(seq(
        sep1(choice(';', $._layout_semicolon), $.field_binding),
        optional(choice(';', $._layout_semicolon)),
      )),
      '}',
    )),

    field_binding: $ => seq(
      field('name', $.variable_identifier),
      '=',
      field('value', $._expression),
    ),

    _fexp: $ => choice(
      $.function_application,
      $._aexp,
    ),

    function_application: $ => prec.left(PREC.APPLY, seq(
      choice($._fexp, $._lexp),
      $._aexp,
    )),

    _aexp: $ => choice(
      $.variable_identifier,
      $.constructor_identifier,
      $._literal,
      $.wildcard,
      $.system_task_identifier,
      $.field_selection,
      $.subscript,
      $.parenthesized_expression,
      $.tuple_expression,
      $.unit_expression,
      $.list_expression,
      $.hash_expression,
      $.section_left,
      $.section_right,
    ),

    system_task_identifier: $ => $._system_task_id,

    field_selection: $ => prec.left(PREC.SELECT, seq(
      $._aexp,
      '.',
      field('field', choice($.variable_identifier, $.integer_literal)),
    )),

    subscript: $ => prec.left(PREC.SELECT, seq(
      $._aexp,
      '[',
      $._expression,
      optional(seq(':', $._expression)),
      ']',
    )),

    parenthesized_expression: $ => seq('(', $._expression, ')'),
    tuple_expression: $ => seq('(', $._expression, ',', sep1(',', $._expression), ')'),
    unit_expression: $ => seq('(', ')'),
    list_expression: $ => seq('[', optional(sep1(',', $._expression)), ']'),
    hash_expression: $ => seq('#', '(', sep1(',', $._expression), ')'),

    section_left: $ => seq('(', $._exp_infix, $.operator, ')'),
    section_right: $ => seq('(', $.operator, $._exp_infix, ')'),

    _statement_block: $ => choice(
      seq('{', optional($._stmts_inner), '}'),
      seq($._layout_open_brace, optional($._stmts_inner), $._layout_close_brace),
    ),

    _stmts_inner: $ => layout_body($, $._statement),

    _statement: $ => choice(
      $.bind_statement,
      $.let_statement,
      $.expression_statement,
    ),

    bind_statement: $ => prec.dynamic(1, seq(
      field('pattern', choice(
        $._apat,
        $.constructor_pattern,
        $.as_pattern,
        $.infix_pattern,
      )),
      optional(seq('::', field('type', $._type))),
      '<-',
      field('value', $._expression),
      optional(seq('when', $._expression)),
    )),

    let_statement: $ => seq(
      choice('let', 'letseq'),
      $._let_bindings,
    ),

    expression_statement: $ => $._expression,

    _pattern: $ => choice(
      $.constructor_pattern,
      $.infix_pattern,
      $._apat,
    ),

    constructor_pattern: $ => prec(PREC.APPLY, seq(
      $.constructor_identifier,
      repeat1($._apat),
    )),

    infix_pattern: $ => prec.left(PREC.INFIX, seq(
      $._pattern,
      $.constructor_symbol,
      $._pattern,
    )),

    as_pattern: $ => seq(
      choice($.variable_identifier, $.wildcard),
      '@',
      $._apat,
    ),

    _apat: $ => choice(
      $.variable_identifier,
      $.constructor_identifier,
      $._literal,
      $.as_pattern,
      $.wildcard,
      $.tuple_pattern,
      $.unit_pattern,
      $.list_pattern,
      $.struct_pattern,
      $.parenthesized_pattern,
    ),

    wildcard: $ => '_',

    tuple_pattern: $ => seq('(', $._pattern, ',', sep1(',', $._pattern), ')'),
    unit_pattern: $ => seq('(', ')'),
    list_pattern: $ => seq('[', optional(sep1(',', $._pattern)), ']'),
    parenthesized_pattern: $ => seq('(', $._pattern, ')'),

    struct_pattern: $ => seq(
      $.constructor_identifier,
      '{',
      optional(sep1(choice(';', $._layout_semicolon, ','), $.field_pattern)),
      '}',
    ),

    field_pattern: $ => seq(
      field('name', $.variable_identifier),
      optional(seq('=', field('pattern', $._pattern))),
    ),

    _literal: $ => choice(
      $.integer_literal,
      $.float_literal,
      $.sized_literal,
      $.char_literal,
      $.string_literal,
    ),

    integer_literal: $ => token(choice(
      /[0-9][0-9_]*/,
      /0[xX][0-9a-fA-F][0-9a-fA-F_]*/,
      /0[oO][0-7][0-7_]*/,
      /0[bB][01][01_]*/,
    )),

    float_literal: $ => token(choice(
      /[0-9][0-9_]*\.[0-9][0-9_]*/,
      /[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*/,
      /[0-9][0-9_]*\.[0-9][0-9_]*[eE][+-]?[0-9][0-9_]*/,
    )),

    sized_literal: $ => token(seq(
      /[0-9][0-9_]*/,
      "'",
      /[hdboHDBO]/,
      /[0-9a-fA-F][0-9a-fA-F_]*/,
    )),

    char_literal: $ => token(seq(
      "'",
      choice(
        /[^\\'\n]/,
        /\\[ntrfv\\"']/,
        /\\x[0-9a-fA-F]+/,
        /\\[0-9]+/,
      ),
      "'",
    )),

    string_literal: $ => token(seq(
      '"',
      repeat(choice(
        /[^\\"\n]/,
        /\\[ntrfv\\"']/,
        /\\x[0-9a-fA-F]+/,
        /\\[0-9]+/,
        /\\&/,
        /\\\s+\\/,
      )),
      '"',
    )),

    variable_identifier: $ => choice($._varid, $.qualified_variable, prec(1, seq('(', $._varsym, ')'))),
    constructor_identifier: $ => choice($._conid, $.qualified_constructor),

    qualified_variable: $ => token(seq(/\p{Lu}[\p{L}\p{N}_']*/u, '.', /[\p{Ll}\p{Lo}\p{Lt}_][\p{L}\p{N}_']*/u)),
    qualified_constructor: $ => token(seq(/\p{Lu}[\p{L}\p{N}_']*/u, '.', /\p{Lu}[\p{L}\p{N}_']*(?:\.\p{Lu}[\p{L}\p{N}_']*)*/u)),

    variable_symbol: $ => $._varsym,
    constructor_symbol: $ => $._consym,

    _varid: $ => token(/[\p{Ll}\p{Lo}\p{Lt}_][\p{L}\p{N}_']*/u),
    _conid: $ => token(/\p{Lu}[\p{L}\p{N}_']*/u),

    _varsym: $ => token(choice(
      /[!@#$%&*+./<=>?\\^|~\-][!@#$%&*+./<=>?\\^|~:\-\u00A2-\u00BF\u00D7\u00F7\p{S}]*/u,
      /[\u00A2-\u00BF\u00D7\u00F7][!@#$%&*+./<=>?\\^|~:\-\u00A2-\u00BF\u00D7\u00F7\p{S}]*/u,
      /[\p{S}][!@#$%&*+./<=>?\\^|~:\-\u00A2-\u00BF\u00D7\u00F7\p{S}]*/u,
    )),
    _consym: $ => token(/:[!@#$%&*+./<=>?\\^|~:\-\u00A2-\u00BF\u00D7\u00F7\p{S}]*/u),

    _system_task_id: $ => token(seq('$', /[a-zA-Z_][a-zA-Z0-9_$]*/)),
  },
});
