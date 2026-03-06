{
  inputs = {
    utils.url = "github:numtide/flake-utils";
    mm0.url = "github:gleachkr/mm0";
  };
  outputs = { self, nixpkgs, mm0, utils }: utils.lib.eachDefaultSystem (system:
    let
      pkgs = nixpkgs.legacyPackages.${system};
      mm0-rs = mm0.packages.${system}.mm0-rs;
      mm0-c = mm0.packages.${system}.mm0-c;
    in
    {
      devShell = pkgs.mkShell {
        buildInputs = with pkgs; [
          zig
          zls
          mm0-rs
          mm0-c
          hyperfine
          perf
        ];
      };
    }
  );
}
