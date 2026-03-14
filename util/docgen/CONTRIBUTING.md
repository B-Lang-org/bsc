# bs-docgen — Contributor Guide

`bs-docgen` is the documentation generator for Bluespec — "Haddock for
Bluespec". It generates a navigable HTML reference website from two sources:

1. **LaTeX reference manual** (`bsc/doc/BH_ref_guide/BH_lang.tex`) — converted
   to HTML via a hand-rolled LaTeX subset parser.
2. **Source doc comments** (`--@` and `-- |` in `.bs`/`.bsv` files) — scraped
   and rendered with cross-linked symbols.

`bbt doc` (in `bbt/`) is a thin wrapper that calls `bs-docgen` with project
sources from `bsc.toml`. All rendering logic lives here.

---

## Repository Layout

```
docgen/
├── docgen.cabal
├── cabal.project            ← references ../lsp/bs-parser
├── app/Main.hs              ← bs-docgen CLI (optparse-applicative)
└── src/Language/Bluespec/DocGen/
    ├── DocAST.hs            ← DocBlock, DocInline, DocEntry, DocKind
    ├── Extract.hs           ← parse Package → collect DocEntry list
    ├── TexParser.hs         ← LaTeX subset → DocAST (megaparsec)
    ├── PlainParser.hs       ← '-- |' plain text → DocAST
    ├── Highlight.hs         ← bs-parser lexer → HTML token spans
    ├── HTML.hs              ← DocAST → blaze-html (per-package pages)
    ├── RefManual.hs         ← LaTeX file → multi-page HTML reference
    ├── SymbolIndex.hs       ← build + resolve cross-reference index
    ├── Generate.hs          ← runDocGen: top-level orchestration
    └── CSS.hs               ← embedded stylesheet (Text literal)
```

---

## Building

```bash
cd /work/bsc/util/docgen
~/.ghcup/bin/cabal build
```

To generate docs for the BSC standard library + reference manual:
```bash
~/.ghcup/bin/cabal run bs-docgen -- \
  --lib-dir /work/bsc/src/Libraries \
  --ref-manual /work/language-bluespec/BH_lang.tex \
  --out /tmp/bsc-docs
```

---

## Architecture

### Data Flow

```
.bs/.bsv source files
  → bs-parser (parseAuto)
  → Extract.hs              builds [DocEntry]
  → SymbolIndex.hs          builds cross-reference map
  → HTML.hs                 renders per-package pages

BH_lang.tex
  → RefManual.hs
      → collectMacros       preamble → \newcommand map
      → expandMacros        substitute known macros
      → parseTexDoc         LaTeX → [DocBlock]
      → splitSections       split on \section boundaries
      → HTML pages          one file per section
```

### DocAST

The intermediate representation (`DocAST.hs`) is shared by both input paths:

```haskell
data DocBlock = Para [DocInline] | Heading Int [DocInline]
              | CodeBlock Language Text | BulletList [[DocBlock]]
              | OrderedList [[DocBlock]] | Table ... | HRule

data DocInline = Plain Text | Code Text | Emph [DocInline]
               | Strong [DocInline] | SymRef Text | NonTerm Text
```

`SymRef` nodes (from `\te{Foo}` or `'Foo'` in `-- |` style) are resolved
to hyperlinks during HTML rendering if the symbol is in the `SymbolIndex`.

### LaTeX Macro Handling

`TexParser.hs` collects `\newcommand` macros from the preamble and expands
them before parsing. Key invariant: **skip macros whose bodies have unbalanced
braces** (e.g. multi-line definitions ending in `{%`). The `balancedBraces`
guard in `collectMacros` enforces this.

`balancedArg` is the core combinator for `{...}` argument parsing — it counts
nested braces. Any change to it should be tested against the full 15-section
reference manual output.

### BSC Commit SHA in Footer

When `--ref-manual` is provided, the generator auto-detects the BSC commit SHA
via `git rev-parse --short HEAD` run in the directory containing `BH_lang.tex`.
Pass `--bsc-sha SHA` explicitly to override this (useful in CI).

---

## Adding Support for a New LaTeX Command

1. In `TexParser.hs`, add a parser for the new command in `inlineCmd` or
   `blockCmd` (depending on whether it produces inline or block content).
2. Map the output to appropriate `DocInline` or `DocBlock` constructors.
3. Test with a snippet from `BH_lang.tex` that uses the command.

If the command is only in the preamble (layout-only), add it to the
`layoutPrefixes` list in `RefManual.hs` instead.

---

## Adding a New Doc Comment Format

Currently supported:
- `--@` lines: LaTeX (BSC library style)
- `-- |` lines: plain text with lightweight markup (Haddock-like)

To add a third format, extend `Extract.hs` (detection of the prefix) and add
a new parser module analogous to `PlainParser.hs`.

---

## Generated Website Structure

```
docs/
├── index.html              ← site root
├── docgen.css              ← single shared stylesheet
├── symbol-index.json       ← JSON index for LSP hover links
├── reference/              ← from BH_lang.tex
│   ├── index.html          ← table of contents
│   ├── identifiers.html    ← one file per \section
│   ├── term-index.html     ← back-of-book alphabetical index
│   └── ...
└── stdlib/                 ← from source doc comments
    ├── index.html          ← package list
    ├── Prelude.html        ← one file per package
    └── ...
```

---

## Known Limitations / Future Work

- Math in doc comments (`$...$`) renders as plain `<code>` (no MathJax).
- Incremental regeneration is not implemented — every run is a full rebuild.
- Instance documentation (provisos) is not yet surfaced.
- `bbt doc --open` flag is not yet implemented.
