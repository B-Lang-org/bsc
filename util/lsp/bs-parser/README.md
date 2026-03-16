# bs-parser — Contributor Guide

`bs-parser` is the Bluespec lexer and parser library shared by `bs-lsp`,
`bs-docgen`, and `bbt`. It handles both Bluespec surface syntaxes:

- **Classic** (`.bs`) — Haskell-like syntax, e.g. `module mkTop = ...`
- **Bluespec SystemVerilog** (`.bsv`) — Verilog-like syntax, e.g. `module mkTop(...); ...`

---

## Repository Layout

```
bs-parser/
├── bs-parser.cabal
├── cabal.project
├── src/Language/Bluespec/
│   ├── Parser.hs           ← Classic parser (parsePackage) + parseAuto dispatch
│   ├── Lexer.hs            ← Classic lexer (scanTokens)
│   ├── Layout.hs           ← Layout-rule token insertion (virtual {, }, ;)
│   ├── Fixity.hs           ← Operator fixity table + Pratt parser
│   ├── Syntax.hs           ← Classic AST types (Package, Defn, Expr, …)
│   ├── Position.hs         ← SrcSpan, SrcPos types
│   ├── Pretty.hs           ← Pretty-printing for types and expressions
│   └── BSV/
│       └── Parser.hs       ← BSV parser (parseBSVPackage) + BSV lexer
└── test/
    └── ParserTest.hs       ← HSpec test suite
```

---

## Building and Testing

```bash
cd util/lsp/bs-parser
~/.ghcup/bin/cabal build
~/.ghcup/bin/cabal test bs-parser-test --test-show-details=always
```

The test suite currently passes 103+ tests across Classic and BSV corpora.

---

## Authoritative References

Before modifying the parser, read the relevant reference material:

| What you're changing | Read first |
|---|---|
| Classic lexer / tokenisation | `/work/bsc/src/comp/Parser/Classic/Lex.hs` |
| Classic parser / AST | `/work/bsc/src/comp/Parser/Classic/CParser.hs`, `CSyntax.hs` |
| Classic language reference | `/work/language-bluespec/BH_lang.tex` (46k+ tokens; read in sections) |
| BSV grammar (EBNF) | `/work/goParseBSV/grammar.txt` |
| BSV parser (Haskell) | `/work/bsc/src/comp/Parser/BSV/CVParser.lhs` |

**Priority**: `CSyntax.hs`/`Lex.hs` take priority over `BH_lang.tex` if they
disagree — the Haskell source is the ground truth for the compiler.

Do **not** modify `/work/language-bluespec/` or `/work/goParseBSV/` — these
are read-only references.

---

## Key Design Decisions

### Error Recovery

The parser uses megaparsec `try` combinators throughout to enable partial parses.
A parse failure on one definition should not block the rest of the file. This
is essential for the LSP use case (files are frequently mid-edit and syntactically
broken).

### Operator Precedence

Classic Bluespec uses user-defined infix operators. The parser reads fixity
declarations and dynamically reconfigures the Pratt parser. See
`ParseOp.hs` and `/work/bsc/src/comp/PreIds.hs` for the default fixity table.

### Dialect Dispatch

`Language.Bluespec.Parser` (top-level) exports `parseAuto`, which inspects
the file extension and delegates to either `parsePackage` (Classic) or
`parseBSVPackage` (BSV). All LSP and docgen callers should use `parseAuto`.

---

## Adding New Syntax

1. Update the relevant AST type in `Syntax.hs` (Classic) or the BSV equivalent.
2. Add a parser combinator in the appropriate `Parser.hs`.
3. Add a test case in `test/ParserTest.hs` using a real or minimal source snippet.
4. Run the full corpus: `cabal test` should still pass 0 failures.

---

## Common Failure Modes

- **Whitespace sensitivity**: Classic is layout-sensitive (like Haskell).
  The lexer inserts virtual `{`, `}`, `;` tokens. Changes to whitespace
  handling ripple through many tests.
- **BSV vs Classic confusion**: some keywords are valid in one dialect but
  not the other. Keep the lexers separate.
