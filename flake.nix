{
  description = "A very basic flake";

  inputs = { nixpkgs.url = "github:nixos/nixpkgs?ref=24.11"; };

  outputs = { self, nixpkgs }:
    let
      pkgs = nixpkgs.legacyPackages.x86_64-linux;
      ghcWithPackages = pkgs.ghc.withPackages
        (g: (with g; [ old-time regex-compat syb split ]));

      yices-src = pkgs.fetchurl {
        url =
          "https://github.com/B-Lang-org/bsc/releases/download/${version}/yices-src-for-bsc-${version}.tar.gz";
        sha256 = "sha256-pyEdCJvmgwOYPMZEtw7aro76tSn/Y/2GcKTyARmIh4E=";
      };
      pname = "bluespec";
      version = "2024.07";
      gmp-static = pkgs.gmp.override { withStatic = true; };
    in {

      packages.x86_64-linux.default = pkgs.stdenv.mkDerivation {

        version = version;
        name = pname;
        src = self;
        enableParallelBuilding = true;

        outputs = [ "out" "doc" ];

        # https://github.com/B-Lang-org/bsc/pull/278 is still applicable, but will probably not be applied as such
        # there is work ongoing: https://github.com/B-Lang-org/bsc/issues/595 https://github.com/B-Lang-org/bsc/pull/600
        patches = [ ./libstp_stub_makefile.patch ];

        postUnpack = ''
          tar -C $sourceRoot/ -xf ${yices-src}
          chmod -R +rwX $sourceRoot/src/vendor/yices/v2.6/yices2
        '';

        preBuild = ''
          patchShebangs \
            src/Verilog/copy_module.pl \
            src/comp/update-build-version.sh \
            src/comp/update-build-system.sh \
            src/comp/wrapper.sh

          substituteInPlace src/comp/Makefile \
            --replace 'BINDDIR' 'BINDIR' \
            --replace 'install-bsc install-bluetcl' 'install-bsc install-bluetcl $(UTILEXES) install-utils'

          # allow running bsc to bootstrap
          export LD_LIBRARY_PATH=$PWD/inst/lib/SAT

          # use more cores for GHC building, 44 causes heap overflows in ghc, and
          # there is not much speedup after 8..
          if [[ $NIX_BUILD_CORES -gt 8 ]] ; then export GHCJOBS=8; else export GHCJOBS=$NIX_BUILD_CORES; fi
        '';

        buildInputs = with pkgs;
          [
            fontconfig
            tcl
            tk
            which
            xorg.libX11 # tcltk
            xorg.libXft
            zlib
          ] ++ yices.buildInputs;

        nativeBuildInputs = with pkgs; [
          automake
          autoconf
          asciidoctor
          bison
          flex
          ghcWithPackages
          perl
          pkg-config
          texliveFull
        ];

        makeFlags = [
          "release"
          "NO_DEPS_CHECKS=1" # skip the subrepo check (this deriviation uses yices-src instead of the subrepo)
          "NOGIT=1" # https://github.com/B-Lang-org/bsc/issues/12
          "LDCONFIG=ldconfig" # https://github.com/B-Lang-org/bsc/pull/43
          "STP_STUB=1" # uses yices as a SMT solver and stub out STP
          "BSC_BUILD=PROF"
        ];

        doCheck = true;

        nativeCheckInputs = with pkgs; [ gmp-static iverilog ];

        checkTarget =
          "check-smoke"; # this is the shortest check but "check-suite" tests much more

        installPhase = ''
          mkdir -p $out
          mv inst/bin $out
          mv inst/lib $out

          # fragile, I know..
          mkdir -p $doc/share/doc/bsc
          mv inst/README $doc/share/doc/bsc
          mv inst/ReleaseNotes.* $doc/share/doc/bsc
          mv inst/doc/*.pdf $doc/share/doc/bsc
        '';
      };
    };
}
