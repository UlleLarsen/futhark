# This default.nix builds a statically linked futhark binary.
#
# It currently does not build documentation and is likely to only work
# on Linux.
#
# Just run 'nix-build' and fish the binary out of 'result/bin/futhark'.

{ nixpkgs ? import <nixpkgs> {},
  compiler ? "ghc883",
  suffix ? "nightly" }:
let
  pkgs = nixpkgs;

  futhark =
    pkgs.haskell.lib.overrideCabal
      (pkgs.haskell.lib.addBuildTools
        (pkgs.haskell.packages.${compiler}.callCabal2nix "futhark"
          ( pkgs.lib.cleanSourceWith { filter = name: type:
                                         baseNameOf (toString name) != "default.nix";
                                       src = pkgs.lib.cleanSource ./.;
                                     })
          { })
        [ pkgs.python37Packages.sphinx ])
    ( _drv: {
      isLibrary = false;
      isExecutable = true;
      enableSharedExecutables = false;
      enableSharedLibraries = false;
      enableLibraryProfiling = false;
      configureFlags = [
        "--ghc-option=-optl=-static"
        "--ghc-option=-split-sections"
        "--extra-lib-dirs=${pkgs.ncurses.override { enableStatic = true; }}/lib"
        "--extra-lib-dirs=${pkgs.glibc.static}/lib"
        "--extra-lib-dirs=${pkgs.gmp6.override { withStatic = true; }}/lib"
        "--extra-lib-dirs=${pkgs.zlib.static}/lib"
        "--extra-lib-dirs=${pkgs.libffi.overrideAttrs (old: { dontDisableStatic = true; })}/lib"
        ];

      postBuild = (_drv.postBuild or "") + ''
        make -C docs man
        '';

      postInstall = (_drv.postInstall or "") + ''
        mkdir -p $out/share/man/man1
        mv docs/_build/man/*.1 $out/share/man/man1/
        '';
      }
    );
in pkgs.stdenv.mkDerivation rec {
  name = "futhark-" + suffix;
  version = futhark.version;
  src = ./.;

  buildInputs = [ futhark ];

  buildPhase = ''
    true
  '';

  installPhase = ''
    mkdir futhark-${suffix}/
    cp -r tools/release/skeleton/* futhark-${suffix}/
    cp -r ${futhark}/bin futhark-${suffix}/bin
    cp -r ${futhark}/share futhark-${suffix}/share
    chmod +w -R futhark-${suffix}
    mkdir -p $out
    tar -Jcf $out/futhark-${suffix}.tar.xz futhark-${suffix}
  '';
}
