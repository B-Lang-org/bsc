[
  "package"
  "where"
  "import"
  "qualified"
  "type"
  "data"
  "struct"
  "class"
  "coherent"
  "incoherent"
  "instance"
  "deriving"
  "interface"
  "module"
  "verilog"
  "rules"
  "when"
  "action"
  "actionvalue"
  "do"
  "let"
  "letseq"
  "in"
  "if"
  "then"
  "else"
  "case"
  "of"
  "foreign"
  "primitive"
  "hiding"
  "valueOf"
  "stringOf"
  "infix"
  "infixl"
  "infixr"
] @keyword

[
  "="
  "::"
  "->"
  "<-"
  "==>"
  "=>"
  "\\"
  "@"
  "|"
  ".."
  ":"
] @operator

(operator) @operator
(variable_symbol) @operator
(constructor_symbol) @operator

(integer_literal) @number
(float_literal) @number.float
(sized_literal) @number
(char_literal) @character
(string_literal) @string

(comment) @comment
(pragma) @attribute

(variable_identifier) @variable
(constructor_identifier) @type
(type_constructor) @type
(type_variable) @type

(module_identifier) @module

(field_selection
  field: (variable_identifier) @property)

(struct_field
  name: (variable_identifier) @property)

(field_declaration
  name: (variable_identifier) @property)

(field_binding
  name: (variable_identifier) @property)

(field_pattern
  name: (variable_identifier) @property)

(interface_binding
  name: (variable_identifier) @property)

(verilog_port_binding
  (variable_identifier) @property)

(function_definition
  name: (variable_identifier) @function)

(type_signature
  name: (variable_identifier) @function)

(type_definition
  name: (constructor_identifier) @type.definition)

(data_definition
  name: (constructor_identifier) @type.definition)

(struct_definition
  name: (constructor_identifier) @type.definition)

(class_definition
  name: (constructor_identifier) @type.definition)

(data_constructor
  name: (constructor_identifier) @constructor)

(system_task_identifier) @function.builtin

(qualified_variable) @variable
(qualified_constructor) @type

(kind_star) @type.builtin
(kind_hash) @type.builtin
(kind_string) @type.builtin

(wildcard) @variable.builtin

(rule
  name: (string_literal) @label)

(deriving_clause
  (constructor_identifier) @type)

((constructor_identifier) @boolean
  (#any-of? @boolean "True" "False"))

(import_declaration
  module: (module_identifier) @module)

[
  "("
  ")"
  "{"
  "}"
  "["
  "]"
] @punctuation.bracket

[
  ","
  ";"
] @punctuation.delimiter
