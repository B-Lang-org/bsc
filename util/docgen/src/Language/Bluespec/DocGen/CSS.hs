-- | Embedded stylesheet for the generated documentation.
module Language.Bluespec.DocGen.CSS
  ( stylesheet
  ) where

import Data.Text (Text)

-- | The single CSS file used across all generated HTML pages.
stylesheet :: Text
stylesheet = "\
\/* bs-docgen stylesheet */\n\
\:root {\n\
\  --bg: #ffffff;\n\
\  --fg: #1a1a2e;\n\
\  --sidebar-bg: #f8f9fb;\n\
\  --border: #dfe3e8;\n\
\  --accent: #2c5282;\n\
\  --kw-color: #2c5282;\n\
\  --ty-color: #1a6b5a;\n\
\  --lit-color: #7c3aed;\n\
\  --op-color: #c53030;\n\
\  --cm-color: #718096;\n\
\  --st-color: #2b6cb0;\n\
\  --link-color: #2b6cb0;\n\
\  --code-bg: #f1f5f9;\n\
\  font-family: 'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif;\n\
\  font-size: 16px;\n\
\  line-height: 1.65;\n\
\  color: var(--fg);\n\
\  background: var(--bg);\n\
\}\n\
\\n\
\body { margin: 0; padding: 0; display: flex; flex-direction: column; min-height: 100vh; }\n\
\\n\
\.page-layout { display: flex; flex: 1; }\n\
\\n\
\nav.sidebar {\n\
\  width: 240px;\n\
\  flex-shrink: 0;\n\
\  background: var(--sidebar-bg);\n\
\  border-right: 1px solid var(--border);\n\
\  padding: 1.25rem 1rem;\n\
\  position: sticky;\n\
\  top: 0;\n\
\  height: 100vh;\n\
\  overflow-y: auto;\n\
\}\n\
\nav.sidebar h2 { font-size: 0.85rem; margin: 0 0 0.75rem 0; text-transform: uppercase; letter-spacing: 0.05em; color: var(--cm-color); }\n\
\nav.sidebar ul { list-style: none; padding: 0; margin: 0; }\n\
\nav.sidebar li { margin: 0.1rem 0; }\n\
\nav.sidebar a { color: var(--fg); text-decoration: none; font-size: 0.88rem; display: block; padding: 0.2rem 0.5rem; border-radius: 4px; }\n\
\nav.sidebar a:hover { background: var(--border); color: var(--link-color); }\n\
\\n\
\main {\n\
\  flex: 1;\n\
\  padding: 2.5rem 3rem;\n\
\  max-width: 880px;\n\
\}\n\
\\n\
\h1 { font-size: 1.75rem; border-bottom: 2px solid var(--accent); padding-bottom: 0.5rem; color: var(--accent); margin-bottom: 1.5rem; }\n\
\h2 { font-size: 1.35rem; margin-top: 2.5rem; margin-bottom: 0.75rem; color: var(--fg); }\n\
\h3 { font-size: 1.1rem; margin-top: 2rem; color: #2d3748; }\n\
\\n\
\/* Prose paragraphs: a touch more breathing room */\n\
\main > p, .doc p, main > ul, main > ol { max-width: 70ch; }\n\
\p { margin: 0.75rem 0; }\n\
\\n\
\section {\n\
\  border-top: 1px solid var(--border);\n\
\  padding-top: 1rem;\n\
\  margin-top: 1.5rem;\n\
\}\n\
\\n\
\pre.type-sig {\n\
\  background: var(--code-bg);\n\
\  border: 1px solid var(--border);\n\
\  border-left: 3px solid var(--accent);\n\
\  padding: 0.6rem 1rem;\n\
\  border-radius: 6px;\n\
\  overflow-x: auto;\n\
\  font-family: 'JetBrains Mono', 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.875rem;\n\
\  line-height: 1.55;\n\
\}\n\
\\n\
\pre {\n\
\  background: var(--code-bg);\n\
\  border: 1px solid var(--border);\n\
\  border-radius: 6px;\n\
\  padding: 1rem 1.25rem;\n\
\  overflow-x: auto;\n\
\  font-family: 'JetBrains Mono', 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.85rem;\n\
\  line-height: 1.6;\n\
\}\n\
\\n\
\code {\n\
\  background: var(--code-bg);\n\
\  border-radius: 4px;\n\
\  padding: 0.15em 0.35em;\n\
\  font-family: 'JetBrains Mono', 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.875em;\n\
\  color: var(--accent);\n\
\}\n\
\pre code { background: none; padding: 0; color: inherit; font-size: inherit; }\n\
\\n\
\.doc { margin-top: 0.5rem; }\n\
\.doc p { margin: 0.5rem 0; }\n\
\\n\
\a { color: var(--link-color); text-decoration: none; }\n\
\a:hover { text-decoration: underline; }\n\
\\n\
\/* Grammar non-terminals: distinct from code */\n\
\em.nt { color: #9b2c2c; font-style: italic; font-weight: 500; }\n\
\\n\
\/* Syntax highlighting */\n\
\.kw { color: var(--kw-color); font-weight: 600; }\n\
\.ty { color: var(--ty-color); }\n\
\.lit { color: var(--lit-color); }\n\
\.op { color: var(--op-color); }\n\
\.cm { color: var(--cm-color); font-style: italic; }\n\
\.st { color: var(--st-color); }\n\
\.id { color: var(--fg); }\n\
\\n\
\/* Tables */\n\
\.doc-table {\n\
\  border-collapse: collapse;\n\
\  width: 100%;\n\
\  margin: 1.25rem 0;\n\
\  font-size: 0.88rem;\n\
\  line-height: 1.5;\n\
\}\n\
\.doc-table th,\n\
\.doc-table td {\n\
\  border: 1px solid var(--border);\n\
\  padding: 0.55rem 0.85rem;\n\
\  text-align: left;\n\
\  vertical-align: top;\n\
\}\n\
\.doc-table th {\n\
\  background: var(--sidebar-bg);\n\
\  font-weight: 600;\n\
\}\n\
\.doc-table tr:nth-child(even) td { background: #fafbfd; }\n\
\.doc-table tr:hover td { background: #edf2f7; }\n\
\.doc-table code {\n\
\  font-size: 0.82em;\n\
\  color: var(--accent);\n\
\}\n\
\\n\
\/* Figures */\n\
\.doc-figure {\n\
\  margin: 2rem 0;\n\
\  text-align: center;\n\
\  padding: 1rem;\n\
\  background: var(--sidebar-bg);\n\
\  border: 1px solid var(--border);\n\
\  border-radius: 8px;\n\
\}\n\
\.doc-figure img {\n\
\  max-width: 100%;\n\
\  height: auto;\n\
\}\n\
\.doc-figure figcaption {\n\
\  margin-top: 0.75rem;\n\
\  font-size: 0.88rem;\n\
\  color: var(--cm-color);\n\
\  font-style: italic;\n\
\}\n\
\\n\
\/* Block quotes */\n\
\blockquote {\n\
\  margin: 1.25rem 0;\n\
\  padding: 0.75rem 1.25rem;\n\
\  border-left: 3px solid var(--accent);\n\
\  background: var(--code-bg);\n\
\  border-radius: 0 6px 6px 0;\n\
\}\n\
\blockquote p { margin: 0.3rem 0; }\n\
\\n\
\/* Footnotes */\n\
\.footnote {\n\
\  font-size: 0.85em;\n\
\  color: var(--cm-color);\n\
\}\n\
\\n\
\/* Lists */\n\
\ul, ol { padding-left: 1.5rem; }\n\
\li { margin: 0.35rem 0; }\n\
\li p { margin: 0.25rem 0; }\n\
\\n\
\/* Heading level 4 (\\paragraph) */\n\
\h4 { font-size: 1rem; margin-top: 1.5rem; margin-bottom: 0.5rem; color: var(--accent); font-weight: 600; }\n\
\\n\
\/* Anchor links on headings */\n\
\.anchor-link {\n\
\  opacity: 0;\n\
\  margin-left: 0.4em;\n\
\  color: var(--cm-color);\n\
\  text-decoration: none;\n\
\  font-weight: 400;\n\
\  transition: opacity 0.15s;\n\
\}\n\
\h1:hover .anchor-link,\n\
\h2:hover .anchor-link,\n\
\h3:hover .anchor-link,\n\
\h4:hover .anchor-link { opacity: 1; }\n\
\.anchor-link:hover { color: var(--link-color); }\n\
\\n\
\/* Breadcrumb navigation */\n\
\.breadcrumb {\n\
\  padding: 0.5rem 1.25rem;\n\
\  font-size: 0.85rem;\n\
\  color: var(--cm-color);\n\
\  border-bottom: 1px solid var(--border);\n\
\  background: #fff;\n\
\  display: flex;\n\
\  align-items: center;\n\
\  gap: 0;\n\
\  flex-wrap: wrap;\n\
\}\n\
\.breadcrumb a { color: var(--link-color); text-decoration: none; }\n\
\.breadcrumb a:hover { text-decoration: underline; }\n\
\.breadcrumb > span:not(.sep) { color: var(--fg); font-weight: 500; }\n\
\.breadcrumb .sep::before { content: '\\203A'; padding: 0 0.5rem; color: var(--cm-color); font-size: 1.1em; }\n\
\\n\
\/* Footer */\n\
\.doc-footer {\n\
\  margin-top: 3rem;\n\
\  padding: 1rem 0;\n\
\  border-top: 1px solid var(--border);\n\
\  color: var(--cm-color);\n\
\  font-size: 0.85rem;\n\
\  text-align: center;\n\
\}\n\
\.doc-footer a { color: var(--cm-color); }\n\
\\n\
\/* Search */\n\
\.search-header {\n\
\  background: var(--accent);\n\
\  border-bottom: 1px solid var(--border);\n\
\  padding: 0.45rem 1.25rem;\n\
\  position: sticky;\n\
\  top: 0;\n\
\  z-index: 100;\n\
\  display: flex;\n\
\  align-items: center;\n\
\}\n\
\.home-btn {\n\
\  color: #fff;\n\
\  font-weight: 700;\n\
\  font-size: 0.95rem;\n\
\  text-decoration: none;\n\
\  white-space: nowrap;\n\
\  margin-right: 1.25rem;\n\
\  padding: 0.2rem 0.5rem;\n\
\  border-radius: 4px;\n\
\  letter-spacing: 0.02em;\n\
\}\n\
\.home-btn:hover { background: rgba(255,255,255,0.15); text-decoration: none; }\n\
\\n\
\.search-container {\n\
\  position: relative;\n\
\  width: 320px;\n\
\}\n\
\.bs-search-input {\n\
\  width: 100%;\n\
\  box-sizing: border-box;\n\
\  padding: 0.4rem 0.75rem;\n\
\  border: 1px solid rgba(255,255,255,0.3);\n\
\  border-radius: 6px;\n\
\  font-size: 0.88rem;\n\
\  background: rgba(255,255,255,0.15);\n\
\  color: #fff;\n\
\  outline: none;\n\
\}\n\
\.bs-search-input::placeholder { color: rgba(255,255,255,0.6); }\n\
\.bs-search-input:focus { background: #fff; color: var(--fg); border-color: #fff; }\n\
\.bs-search-input:focus::placeholder { color: var(--cm-color); }\n\
\.bs-search-results {\n\
\  position: absolute;\n\
\  top: calc(100% + 2px);\n\
\  left: 0;\n\
\  right: 0;\n\
\  background: var(--bg);\n\
\  border: 1px solid var(--border);\n\
\  border-radius: 4px;\n\
\  box-shadow: 0 4px 12px rgba(0,0,0,.15);\n\
\  list-style: none;\n\
\  margin: 0;\n\
\  padding: 0;\n\
\  z-index: 200;\n\
\  max-height: 380px;\n\
\  overflow-y: auto;\n\
\}\n\
\.bs-search-results li a {\n\
\  display: flex;\n\
\  justify-content: space-between;\n\
\  align-items: center;\n\
\  padding: 0.35rem 0.75rem;\n\
\  text-decoration: none;\n\
\  color: var(--fg);\n\
\  font-size: 0.9rem;\n\
\  gap: 1rem;\n\
\}\n\
\.bs-search-results li a:hover,\n\
\.bs-search-results li a:focus { background: var(--sidebar-bg); outline: none; }\n\
\.bs-pkg { color: var(--cm-color); font-size: 0.8em; white-space: nowrap; }\n\
\.bs-no-match { padding: 0.35rem 0.75rem; color: var(--cm-color); font-size: 0.9rem; }\n\
\\n\
\/* Subsection split-page layout: sidebar + main content */\n\
\.sub-layout {\n\
\  display: flex;\n\
\  flex: 1;\n\
\  gap: 0;\n\
\}\n\
\.sub-sidebar {\n\
\  width: 240px;\n\
\  flex-shrink: 0;\n\
\  background: var(--sidebar-bg);\n\
\  border-right: 1px solid var(--border);\n\
\  padding: 1.25rem 1rem;\n\
\  position: sticky;\n\
\  top: 0;\n\
\  height: 100vh;\n\
\  overflow-y: auto;\n\
\  box-sizing: border-box;\n\
\}\n\
\.sub-sidebar h3 { font-size: 0.8rem; margin: 0 0 0.75rem 0; color: var(--cm-color); text-transform: uppercase; letter-spacing: 0.06em; font-weight: 600; }\n\
\.sub-sidebar ul { list-style: none; padding: 0; margin: 0; }\n\
\.sub-sidebar li { margin: 0.1rem 0; }\n\
\.sub-sidebar a { color: var(--fg); text-decoration: none; font-size: 0.85rem; display: block; padding: 0.25rem 0.5rem; border-radius: 4px; }\n\
\.sub-sidebar a:hover { background: var(--border); color: var(--link-color); }\n\
\.sub-sidebar li.active > a { font-weight: 600; color: var(--accent); background: #e8edf3; }\n\
\.sub-layout > main { min-width: 0; }\n\
\"
