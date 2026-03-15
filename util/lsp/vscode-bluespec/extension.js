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

// Build LanguageClient options from current configuration.
function buildClientOptions(config) {
  const configuredPath = config.get('serverPath', 'bs-lsp');
  const extraEnv       = config.get('serverEnv', {});
  const debugMode      = config.get('debugMode', false);
  const debugLogPath   = config.get('debugLogPath', '/tmp/bs-lsp-debug.log');

  let serverPath = configuredPath;
  if (configuredPath === 'bs-lsp') {
    serverPath = findBesideBsc() ?? 'bs-lsp';
  }

  // Inject BS_LSP_DEBUG when debug mode is enabled
  const debugEnv = debugMode ? { BS_LSP_DEBUG: debugLogPath || '/tmp/bs-lsp-debug.log' } : {};

  const serverOptions = {
    command: serverPath,
    transport: TransportKind.stdio,
    options: {
      env: Object.assign({}, process.env, extraEnv, debugEnv),
    },
  };

  return serverOptions;
}

async function startClient(context) {
  const config = vscode.workspace.getConfiguration('bluespec');
  const serverOptions = buildClientOptions(config);

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

  await client.start();

  // Notify the user where the debug log is being written
  const debugMode    = config.get('debugMode', false);
  const debugLogPath = config.get('debugLogPath', '/tmp/bs-lsp-debug.log');
  if (debugMode) {
    const logPath = debugLogPath || '/tmp/bs-lsp-debug.log';
    vscode.window.showInformationMessage(
      `Bluespec LSP debug mode ON — logging JSON-RPC traffic to: ${logPath}`
    );
  }
}

async function stopClient() {
  if (client) {
    await client.stop();
    client = undefined;
  }
}

function activate(context) {
  startClient(context);

  // Command: Bluespec: Restart Language Server
  context.subscriptions.push(
    vscode.commands.registerCommand('bluespec.restartServer', async () => {
      await stopClient();
      await startClient(context);
      vscode.window.showInformationMessage('Bluespec language server restarted.');
    })
  );

  // Auto-restart when debug settings change
  context.subscriptions.push(
    vscode.workspace.onDidChangeConfiguration(async (event) => {
      const affected =
        event.affectsConfiguration('bluespec.debugMode') ||
        event.affectsConfiguration('bluespec.debugLogPath') ||
        event.affectsConfiguration('bluespec.serverPath') ||
        event.affectsConfiguration('bluespec.serverEnv');

      if (affected) {
        await stopClient();
        await startClient(context);
      }
    })
  );
}

function deactivate() {
  return stopClient();
}

module.exports = { activate, deactivate };
