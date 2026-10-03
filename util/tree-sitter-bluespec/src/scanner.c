/*
 * External scanner for Bluespec Classic tree-sitter grammar.
 *
 * Handles Haskell-style layout rules (indentation-sensitive syntax)
 * by injecting virtual open-braces, close-braces, and semicolons.
 * Also handles comments, pragmas, and C preprocessor lines.
 */

#include "tree_sitter/parser.h"

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

// External token IDs — must match the order in grammar.js externals
enum TokenType {
  LAYOUT_OPEN_BRACE,
  LAYOUT_CLOSE_BRACE,
  LAYOUT_SEMICOLON,
  EMPTY_LAYOUT,
  COMMENT,
  PRAGMA,
  CPP_LINE,
  INTERFACE_LAYOUT_OPEN,
};

// Maximum indent stack depth
#define MAX_INDENT_STACK 256

typedef struct {
  uint16_t indent_stack[MAX_INDENT_STACK];
  uint8_t stack_size;
} Scanner;

static void push_indent(Scanner *scanner, uint16_t indent) {
  if (scanner->stack_size < MAX_INDENT_STACK) {
    scanner->indent_stack[scanner->stack_size++] = indent;
  }
}

static void pop_indent(Scanner *scanner) {
  if (scanner->stack_size > 0) {
    scanner->stack_size--;
  }
}

static uint16_t current_indent(Scanner *scanner) {
  if (scanner->stack_size > 0) {
    return scanner->indent_stack[scanner->stack_size - 1];
  }
  return 0;
}

void *tree_sitter_bluespec_external_scanner_create(void) {
  Scanner *scanner = calloc(1, sizeof(Scanner));
  return scanner;
}

void tree_sitter_bluespec_external_scanner_destroy(void *payload) {
  free(payload);
}

unsigned tree_sitter_bluespec_external_scanner_serialize(void *payload,
                                                         char *buffer) {
  Scanner *scanner = (Scanner *)payload;
  unsigned size = 0;

  buffer[size++] = (char)scanner->stack_size;
  for (uint8_t i = 0; i < scanner->stack_size; i++) {
    buffer[size++] = (char)(scanner->indent_stack[i] & 0xFF);
    buffer[size++] = (char)((scanner->indent_stack[i] >> 8) & 0xFF);
  }
  return size;
}

void tree_sitter_bluespec_external_scanner_deserialize(void *payload,
                                                       const char *buffer,
                                                       unsigned length) {
  Scanner *scanner = (Scanner *)payload;
  scanner->stack_size = 0;

  if (length == 0)
    return;

  unsigned pos = 0;
  scanner->stack_size = (uint8_t)buffer[pos++];

  for (uint8_t i = 0; i < scanner->stack_size && pos + 1 < length; i++) {
    scanner->indent_stack[i] = (uint16_t)((uint8_t)buffer[pos]) |
                               ((uint16_t)((uint8_t)buffer[pos + 1]) << 8);
    pos += 2;
  }
}

static void advance(TSLexer *lexer) { lexer->advance(lexer, false); }

static void skip(TSLexer *lexer) { lexer->advance(lexer, true); }

static bool is_newline(int32_t c) { return c == '\n' || c == '\r'; }

// Characters that can continue an operator symbol (after the first char).
// Matches isSym continuation chars from BSC Lex.hs.
static bool is_sym_continuation(int32_t c) {
  switch (c) {
  case '!':
  case '#':
  case '$':
  case '%':
  case '&':
  case '*':
  case '+':
  case '.':
  case '/':
  case '<':
  case '=':
  case '>':
  case '?':
  case '\\':
  case '^':
  case '|':
  case '~':
  case ':':
    return true;
  default:
    return false;
  }
}

// Skip whitespace but stop at newlines; return the column after skipping.
// If we cross a newline, return the column of the first non-whitespace on the
// new line.
static bool skip_whitespace_and_newlines(TSLexer *lexer,
                                         bool *crossed_newline) {
  *crossed_newline = false;
  while (!lexer->eof(lexer)) {
    if (lexer->lookahead == ' ') {
      skip(lexer);
    } else if (lexer->lookahead == '\t') {
      skip(lexer);
    } else if (is_newline(lexer->lookahead)) {
      *crossed_newline = true;
      skip(lexer);
    } else {
      break;
    }
  }
  return true;
}

static bool scan_line_comment(TSLexer *lexer) {
  // We've already confirmed '--'
  // Consume until end of line
  while (!lexer->eof(lexer) && !is_newline(lexer->lookahead)) {
    advance(lexer);
  }
  lexer->mark_end(lexer);
  lexer->result_symbol = COMMENT;
  return true;
}

static bool scan_block_comment(TSLexer *lexer) {
  // We've consumed '{-', now consume until matching '-}'
  // Handle nesting
  int depth = 1;
  while (!lexer->eof(lexer) && depth > 0) {
    if (lexer->lookahead == '{') {
      advance(lexer);
      if (lexer->lookahead == '-') {
        advance(lexer);
        depth++;
      }
    } else if (lexer->lookahead == '-') {
      advance(lexer);
      if (lexer->lookahead == '}') {
        advance(lexer);
        depth--;
      }
    } else {
      advance(lexer);
    }
  }
  lexer->mark_end(lexer);
  lexer->result_symbol = COMMENT;
  return true;
}

static bool scan_pragma(TSLexer *lexer) {
  // We've consumed '{-#', now consume until '#-}'
  int depth = 1;
  while (!lexer->eof(lexer) && depth > 0) {
    if (lexer->lookahead == '#') {
      advance(lexer);
      if (lexer->lookahead == '-') {
        advance(lexer);
        if (lexer->lookahead == '}') {
          advance(lexer);
          depth--;
        }
      }
    } else if (lexer->lookahead == '{') {
      advance(lexer);
      if (lexer->lookahead == '-') {
        advance(lexer);
        if (lexer->lookahead == '#') {
          advance(lexer);
          depth++;
        }
      }
    } else {
      advance(lexer);
    }
  }
  lexer->mark_end(lexer);
  lexer->result_symbol = PRAGMA;
  return true;
}

static bool scan_cpp_line(TSLexer *lexer) {
  // Consume the rest of the line (we've already seen '#' at col 0)
  while (!lexer->eof(lexer) && !is_newline(lexer->lookahead)) {
    advance(lexer);
  }
  lexer->mark_end(lexer);
  lexer->result_symbol = CPP_LINE;
  return true;
}

bool tree_sitter_bluespec_external_scanner_scan(void *payload, TSLexer *lexer,
                                                const bool *valid_symbols) {
  Scanner *scanner = (Scanner *)payload;

  // If we're in error recovery, don't inject tokens
  if (valid_symbols[LAYOUT_OPEN_BRACE] && valid_symbols[LAYOUT_CLOSE_BRACE] &&
      valid_symbols[LAYOUT_SEMICOLON] && valid_symbols[EMPTY_LAYOUT] &&
      valid_symbols[COMMENT] && valid_symbols[PRAGMA] &&
      valid_symbols[CPP_LINE] && valid_symbols[INTERFACE_LAYOUT_OPEN]) {
    return false;
  }

  // Track whether we've crossed a newline
  bool crossed_newline = false;

  // Remember start position
  lexer->mark_end(lexer);

  // Skip whitespace, tracking newlines
  skip_whitespace_and_newlines(lexer, &crossed_newline);

  // Check for EOF
  if (lexer->eof(lexer)) {
    // If layout open is requested at EOF, produce empty layout
    if ((valid_symbols[LAYOUT_OPEN_BRACE] ||
         valid_symbols[INTERFACE_LAYOUT_OPEN]) &&
        valid_symbols[EMPTY_LAYOUT]) {
      lexer->result_symbol = EMPTY_LAYOUT;
      return true;
    }
    // Close any remaining layout contexts
    if (valid_symbols[LAYOUT_CLOSE_BRACE] && scanner->stack_size > 0) {
      pop_indent(scanner);
      lexer->result_symbol = LAYOUT_CLOSE_BRACE;
      return true;
    }
    return false;
  }

  // Get the current column
  uint32_t column = lexer->get_column(lexer);

  // CPP line: # at column 0 followed by a space or digit
  if (valid_symbols[CPP_LINE] && column == 0 && lexer->lookahead == '#') {
    advance(lexer);
    if (lexer->lookahead == ' ' ||
        (lexer->lookahead >= '0' && lexer->lookahead <= '9')) {
      return scan_cpp_line(lexer);
    }
    // Not a CPP line; we consumed '#' but that might be a hash operator
    // Don't mark_end, let the lexer handle it
    return false;
  }

  // Comment / pragma detection
  if (valid_symbols[COMMENT] || valid_symbols[PRAGMA]) {
    if (lexer->lookahead == '-') {
      advance(lexer);
      if (lexer->lookahead == '-') {
        advance(lexer);
        // Make sure it's not an operator like -->, --->, etc.
        // A line comment is -- followed by:
        // - end of line/file
        // - a non-symbol character
        // - another '-' (i.e., ---)
        // A line comment is -- NOT followed by a symbol char
        // (otherwise it's an operator like -->)
        if (lexer->eof(lexer) || is_newline(lexer->lookahead) ||
            lexer->lookahead == '-' || !is_sym_continuation(lexer->lookahead)) {
          lexer->mark_end(lexer);
          return scan_line_comment(lexer);
        }
      }
      // Not a comment
      return false;
    }

    if (lexer->lookahead == '{') {
      advance(lexer);
      if (lexer->lookahead == '-') {
        advance(lexer);
        if (lexer->lookahead == '#') {
          if (valid_symbols[PRAGMA]) {
            advance(lexer);
            lexer->mark_end(lexer);
            return scan_pragma(lexer);
          }
        }
        // Block comment
        if (valid_symbols[COMMENT]) {
          lexer->mark_end(lexer);
          return scan_block_comment(lexer);
        }
      }
      return false;
    }
  }

  // Layout: emit virtual close brace if column is less than current indent
  if (valid_symbols[LAYOUT_CLOSE_BRACE] && scanner->stack_size > 0) {
    if (crossed_newline && column < current_indent(scanner)) {
      pop_indent(scanner);
      lexer->result_symbol = LAYOUT_CLOSE_BRACE;
      return true;
    }
    // Also close on certain tokens that would end a layout block
    if (lexer->lookahead == ')' || lexer->lookahead == ']') {
      pop_indent(scanner);
      lexer->result_symbol = LAYOUT_CLOSE_BRACE;
      return true;
    }
    // Close layout when we encounter keywords that terminate blocks
    // like 'in' (terminates let), 'of' (terminates case scrutinee), etc.
    if (lexer->lookahead == 'i') {
      // Could be 'in' or 'interface' or 'import' etc.
      // We peek ahead without consuming
      lexer->mark_end(lexer);
      advance(lexer);
      if (lexer->lookahead == 'n' && !lexer->eof(lexer)) {
        advance(lexer);
        // Check it's 'in' followed by non-identifier char
        if (lexer->eof(lexer) ||
            !((lexer->lookahead >= 'a' && lexer->lookahead <= 'z') ||
              (lexer->lookahead >= 'A' && lexer->lookahead <= 'Z') ||
              (lexer->lookahead >= '0' && lexer->lookahead <= '9') ||
              lexer->lookahead == '_' || lexer->lookahead == '\'')) {
          pop_indent(scanner);
          lexer->result_symbol = LAYOUT_CLOSE_BRACE;
          return true;
        }
      }
    }
  }

  // Layout: emit virtual semicolon at same indent level after newline
  if (valid_symbols[LAYOUT_SEMICOLON] && scanner->stack_size > 0) {
    if (crossed_newline && column == current_indent(scanner)) {
      lexer->result_symbol = LAYOUT_SEMICOLON;
      return true;
    }
  }

  // Layout: open a new layout context (module interface variant)
  // Used only by module_interface's no-type-name form.
  // Skips '(' and uppercase letters so the grammar can first try the
  // tuple form 'interface (a, b)' or the with-type-name form
  // 'interface Foo { bindings }' before falling back to layout.
  if (valid_symbols[INTERFACE_LAYOUT_OPEN]) {
    if (lexer->lookahead == '{') {
      return false;
    }
    if (lexer->lookahead == '(' ||
        (lexer->lookahead >= 'A' && lexer->lookahead <= 'Z')) {
      return false;
    }
    if (valid_symbols[EMPTY_LAYOUT]) {
      if (scanner->stack_size > 0 && column <= current_indent(scanner)) {
        lexer->result_symbol = EMPTY_LAYOUT;
        return true;
      }
    }
    push_indent(scanner, column);
    lexer->result_symbol = INTERFACE_LAYOUT_OPEN;
    return true;
  }

  // Layout: open a new layout context (general)
  if (valid_symbols[LAYOUT_OPEN_BRACE]) {
    if (lexer->lookahead == '{') {
      return false;
    }

    // Don't open layout for 'module verilog' — peek for the keyword
    if (!crossed_newline && lexer->lookahead == 'v') {
      lexer->mark_end(lexer);
      const char *kw = "verilog";
      bool match = true;
      for (int i = 0; kw[i] && match; i++) {
        if (lexer->lookahead != kw[i])
          match = false;
        else
          advance(lexer);
      }
      if (match && (lexer->eof(lexer) || lexer->lookahead == ' ' ||
                    lexer->lookahead == '\t' || is_newline(lexer->lookahead))) {
        return false;
      }
      // Not 'verilog' — fall through to open layout
    }

    if (valid_symbols[EMPTY_LAYOUT]) {
      if (scanner->stack_size > 0 && column <= current_indent(scanner)) {
        lexer->result_symbol = EMPTY_LAYOUT;
        return true;
      }
    }

    push_indent(scanner, column);
    lexer->result_symbol = LAYOUT_OPEN_BRACE;
    return true;
  }

  return false;
}
