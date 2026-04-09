{
  inputs = {
    nixpkgs.url = "nixpkgs";
    utils.url = "github:numtide/flake-utils";
    mm0.url = "github:gleachkr/mm0";
  };

  outputs = { self, nixpkgs, mm0, utils }:
    utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        mm0-rs = mm0.packages.${system}.mm0-rs;
        mm0-c = mm0.packages.${system}.mm0-c;
        zig = pkgs.zig;
        deps = zig.fetchDeps {
          pname = "mm0-zig";
          version = "0.0.0";
          src = self;
          hash = "sha256-tMfArbqVNjHRRrJdBrln/9tCT40ZZPNJg27fIO9VUHw=";
        };
        package = pkgs.stdenvNoCC.mkDerivation {
          pname = "mm0-zig";
          version = "0.0.0";
          src = self;

          nativeBuildInputs = [ zig ];

          dontSetZigDefaultFlags = true;
          zigBuildFlags = [
            "-Dcpu=baseline"
            "-Doptimize=ReleaseFast"
          ];

          postConfigure = ''
            ln -s ${deps} $ZIG_GLOBAL_CACHE_DIR/p
          '';
        };
      in
      rec {
        packages.default = package;
        defaultPackage = packages.default;

        devShells.default = pkgs.mkShell {
          buildInputs = with pkgs; [
            zig
            zls
            mm0-rs
            mm0-c
            hyperfine
            perf
          ];
        };
        devShell = devShells.default;
      }
    );
}
