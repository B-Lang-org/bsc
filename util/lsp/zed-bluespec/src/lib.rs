use zed_extension_api::{self as zed, LanguageServerId, Result};

struct BluespecExtension;

impl zed::Extension for BluespecExtension {
    fn new() -> Self {
        BluespecExtension
    }

    fn language_server_command(
        &mut self,
        _language_server_id: &LanguageServerId,
        _worktree: &zed::Worktree,
    ) -> Result<zed::Command> {
        // bs-lsp must be on PATH (e.g. built from bsc and installed via
        // `make install` or `cabal install`).  Users can override the binary
        // path in their Zed settings:
        //
        //   "lsp": {
        //     "bs-lsp": {
        //       "binary": { "path": "/path/to/bs-lsp" }
        //     }
        //   }
        Ok(zed::Command {
            command: "bs-lsp".into(),
            args: vec![],
            env: Default::default(),
        })
    }
}

zed::register_extension!(BluespecExtension);
