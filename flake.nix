{
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";

    apalache-release = {
      url =
        "https://github.com/informalsystems/apalache/releases/download/v0.44.10/apalache.zip";
      flake = false;
      type = "tarball";
    };

    poetry2nix.url = "github:nix-community/poetry2nix";
  };

  outputs = { self, nixpkgs, flake-utils, poetry2nix, ... }@inputs:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };

        apalache = pkgs.stdenv.mkDerivation {
          name = "apalache";
          src = inputs.apalache-release;

          buildInputs = [ pkgs.makeWrapper ];

          installPhase = ''
                mkdir -p $out
                cp -r lib $out/lib

                mkdir -p $out/bin
                cat > $out/bin/apalache-mc <<- EOM
                #!${pkgs.bash}/bin/bash
                exec ${pkgs.jre}/bin/java -Xmx100G -jar "$out/lib/apalache.jar" "\$@"
                EOM
                chmod +x $out/bin/apalache-mc
          '';

          postFixup = ''
            wrapProgram $out/bin/apalache-mc \
            --set PATH ${pkgs.lib.makeBinPath [ pkgs.gcc12 pkgs.z3 ]}
          '';
        };

        p2n = poetry2nix.lib.mkPoetry2Nix { inherit pkgs; };
        python = pkgs.python311;
        pypkgs = pkgs.python311Packages;

        poetryEnv = p2n.mkPoetryEnv {
          inherit python;
          projectDir = ./.;
          overrides = p2n.defaultPoetryOverrides.extend
            (self: super: {
              pyeda = super.pyeda.overridePythonAttrs
              (old: {
                buildInputs = (old.buildInputs or []) ++ [super.setuptools];
              });
              dot2tex = pypkgs.dot2tex; # poetry version fails...
            });
        };
      in {
        devShell = pkgs.mkShell { 
          buildInputs = [ 
            pkgs.tlaplus
            apalache 
            poetryEnv
            pkgs.poetry
          ]; 
        };
      });
}

