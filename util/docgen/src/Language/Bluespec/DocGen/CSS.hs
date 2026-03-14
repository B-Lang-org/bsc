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
\  --fg: #24292e;\n\
\  --sidebar-bg: #f6f8fa;\n\
\  --border: #e1e4e8;\n\
\  --kw-color: #005cc5;\n\
\  --ty-color: #005073;\n\
\  --lit-color: #6f42c1;\n\
\  --op-color: #d73a49;\n\
\  --cm-color: #6a737d;\n\
\  --st-color: #032f62;\n\
\  --link-color: #0366d6;\n\
\  font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', Helvetica, Arial, sans-serif;\n\
\  font-size: 16px;\n\
\  line-height: 1.5;\n\
\  color: var(--fg);\n\
\  background: var(--bg);\n\
\}\n\
\\n\
\body { margin: 0; padding: 0; display: flex; flex-direction: column; min-height: 100vh; }\n\
\\n\
\.page-layout { display: flex; flex: 1; }\n\
\\n\
\nav.sidebar {\n\
\  width: 220px;\n\
\  flex-shrink: 0;\n\
\  background: var(--sidebar-bg);\n\
\  border-right: 1px solid var(--border);\n\
\  padding: 1rem;\n\
\  position: sticky;\n\
\  top: 0;\n\
\  height: 100vh;\n\
\  overflow-y: auto;\n\
\}\n\
\nav.sidebar h2 { font-size: 1rem; margin: 0 0 0.5rem 0; }\n\
\nav.sidebar ul { list-style: none; padding: 0; margin: 0; }\n\
\nav.sidebar li { margin: 0.2rem 0; }\n\
\nav.sidebar a { color: var(--link-color); text-decoration: none; }\n\
\nav.sidebar a:hover { text-decoration: underline; }\n\
\\n\
\main {\n\
\  flex: 1;\n\
\  padding: 2rem;\n\
\  max-width: 860px;\n\
\}\n\
\\n\
\h1 { font-size: 1.6rem; border-bottom: 1px solid var(--border); padding-bottom: 0.5rem; }\n\
\h2 { font-size: 1.3rem; margin-top: 2rem; }\n\
\h3 { font-size: 1.1rem; margin-top: 1.5rem; color: #444; }\n\
\\n\
\section {\n\
\  border-top: 1px solid var(--border);\n\
\  padding-top: 1rem;\n\
\  margin-top: 1rem;\n\
\}\n\
\\n\
\pre.type-sig {\n\
\  background: var(--sidebar-bg);\n\
\  border: 1px solid var(--border);\n\
\  border-left: 4px solid var(--link-color);\n\
\  padding: 0.5rem 1rem;\n\
\  border-radius: 4px;\n\
\  overflow-x: auto;\n\
\  font-family: 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.9rem;\n\
\}\n\
\\n\
\pre {\n\
\  background: #f6f8fa;\n\
\  border: 1px solid var(--border);\n\
\  border-radius: 4px;\n\
\  padding: 1rem;\n\
\  overflow-x: auto;\n\
\  font-family: 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.88rem;\n\
\}\n\
\\n\
\code {\n\
\  background: var(--sidebar-bg);\n\
\  border-radius: 3px;\n\
\  padding: 0.1em 0.3em;\n\
\  font-family: 'SFMono-Regular', Consolas, 'Liberation Mono', Menlo, monospace;\n\
\  font-size: 0.9em;\n\
\}\n\
\\n\
\.doc { margin-top: 0.5rem; }\n\
\.doc p { margin: 0.5rem 0; }\n\
\\n\
\a { color: var(--link-color); }\n\
\a:hover { text-decoration: underline; }\n\
\\n\
\/* Syntax highlighting */\n\
\.kw { color: var(--kw-color); font-weight: bold; }\n\
\.ty { color: var(--ty-color); }\n\
\.lit { color: var(--lit-color); }\n\
\.op { color: var(--op-color); }\n\
\.cm { color: var(--cm-color); font-style: italic; }\n\
\.st { color: var(--st-color); }\n\
\.id { color: var(--fg); }\n\
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
\"
