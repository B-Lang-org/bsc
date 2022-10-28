# Haskell Language Server
The following instructions are helpful if you wish to develop on the haskell sources for bluespec.

Once you've got ``bsc`` compiled, usually by running ``make install-src`` at the root of this repository, you can run ``python3 util/haskell-language-server/gen_hie.py`` which should generate and place a proper ``hie.yaml`` in ``./src/comp``.

You can then open up ``src/comp`` as a workspace in your favorite IDE or editor that has [HLS](https://github.com/haskell/haskell-language-server) support.

# Dependencies

``pip3 install pyyaml``