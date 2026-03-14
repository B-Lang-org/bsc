'use strict';

const vscode = require('vscode');
const { LanguageClient, TransportKind } = require('vscode-languageclient/node');

let client;

function activate(context) {
  const config = vscode.workspace.getConfiguration('bluespec');
  const serverPath = config.get('serverPath', 'bs-lsp');
  const extraEnv = config.get('serverEnv', {});

  const serverOptions = {
    command: serverPath,
    transport: TransportKind.stdio,
    options: {
      env: Object.assign({}, process.env, extraEnv),
    },
  };

  const clientOptions = {
    documentSelector: [{ scheme: 'file', language: 'bluespec' }],
    synchronize: {
      fileEvents: vscode.workspace.createFileSystemWatcher('**/*.bs'),
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
