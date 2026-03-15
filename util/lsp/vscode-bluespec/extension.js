'use strict';

const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');
const { execFileSync } = require('child_process');
const path = require('path');
const fs = require('fs');

let client;

// Locate bs-lsp by spawning a login shell so it inherits the user's full PATH.
// Returns null if bsc/bs-lsp cannot be found.
function findBesideBsc() {
  if (process.platform === 'win32') return null;
  try {
    const shell = process.env.SHELL || '/bin/sh';
    const bscPath = execFileSync(shell, ['-lc', 'which bsc'], {
      encoding: 'utf8',
      timeout: 5000,
    }).trim().split('\n')[0];
    const candidate = path.join(path.dirname(bscPath), 'bs-lsp');
    if (fs.existsSync(candidate)) return candidate;
  } catch (_) { /* bsc not found */ }
  return null;
}

function activate(context) {
  const config = vscode.workspace.getConfiguration('bluespec');
  const configuredPath = config.get('serverPath', 'bs-lsp');
  const extraEnv = config.get('serverEnv', {});

  // If the user left serverPath at the default, try to auto-locate bs-lsp
  // next to the bsc binary via a login shell.
  let serverPath = configuredPath;
  if (configuredPath === 'bs-lsp') {
    serverPath = findBesideBsc() ?? 'bs-lsp';
  }

  const serverOptions = {
    command: serverPath,
    transport: TransportKind.stdio,
    options: {
      env: Object.assign({}, process.env, extraEnv),
    },
  };

  const clientOptions = {
    documentSelector: [
      { scheme: 'file', language: 'bluespec' },
      { scheme: 'file', language: 'bluespec-sv' },
    ],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher('**/*.{bs,bsv}'),
    },
    traceOutputChannel: vscode.window.createOutputChannel('Bluespec LSP Trace'),
  };

  client = new LanguageClient(
    'bluespec',
    'Bluespec Language Server',
    serverOptions,
    clientOptions
  );

  client.start();
}

function deactivate() {
  if (!client) return undefined;
  return client.stop();
}

module.exports = { activate, deactivate };
