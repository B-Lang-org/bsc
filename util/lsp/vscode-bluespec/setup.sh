#!/usr/bin/env bash
# Install the vscode-bluespec extension for development/testing.
# Run this once after cloning or after editing package.json.

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
VSCODE_EXT_DIR="$HOME/.vscode/extensions/vscode-bluespec-0.0.1"

cd "$SCRIPT_DIR"

echo "Installing npm dependencies..."
npm install

echo "Copying extension to $VSCODE_EXT_DIR ..."
rm -rf "$VSCODE_EXT_DIR"
mkdir -p "$VSCODE_EXT_DIR"
cp -r extension.js language-configuration.json package.json syntaxes node_modules "$VSCODE_EXT_DIR/"

echo ""
echo "Done! Restart VS Code (or run 'Developer: Reload Window') to activate."
echo ""
echo "Make sure bs-lsp is on your PATH, or set 'bluespec.serverPath' in"
echo "VS Code settings to the full path of the bs-lsp binary."
echo ""
echo "To set BLUESPECDIR so bs-lsp can find the standard library, either:"
echo "  export BLUESPECDIR=/path/to/bsc/inst"
echo "  or add it to 'bluespec.serverEnv' in VS Code settings:"
echo '  { "bluespec.serverEnv": { "BLUESPECDIR": "/path/to/bsc/inst" } }'
