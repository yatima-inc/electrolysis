{
  description = "Electrolysis for verifying rust programs";

  inputs = {
    lean = {
      url = "github:leanprover/lean4";
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-21.11";
    flake-utils = {
      url = "github:numtide/flake-utils";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    naersk = {
      url = github:nix-community/naersk;
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, lean, flake-utils, nixpkgs, naersk }:
    let
      supportedSystems = [
        "aarch64-linux"
        "aarch64-darwin"
        "i686-linux"
        "x86_64-darwin"
        "x86_64-linux"
      ];
      inherit (flake-utils) lib;
    in
    lib.eachSystem supportedSystems (system:
      let
        leanPkgs = lean.packages.${system};
        pkgs = nixpkgs.legacyPackages.${system};
        rustTools = import ./nix/rust.nix {
          nixpkgs = pkgs;
        };
        getRust =
          { channel ? "nightly"
          , date
          , sha256
          , targets ? [ "wasm32-unknown-unknown" "wasm32-wasi" "wasm32-unknown-emscripten" ]
          }: (rustTools.rustChannelOf {
            inherit channel date sha256;
          }).rust.override {
            inherit targets;
            extensions = [ "rust-src" "rust-analysis" ];
          };
        # This is the version used across projects
        rust2022-02-20 = getRust { date = "2022-02-20"; sha256 = "sha256-ZptNrC/0Eyr0c3IiXVWTJbuprFHq6E1KfBgqjGQBIRs="; };
        rust2022-03-15 = getRust { date = "2022-03-15"; sha256 = "sha256-C7X95SGY0D7Z17I8J9hg3z9cRnpXP7FjAOkvEdtB9nE="; };
        rust = rust2022-03-15;
        # Get a naersk with the input rust version
        naerskWithRust = rust: naersk.lib."${system}".override {
          rustc = rust;
          cargo = rust;
        };
        buildRustProject = pkgs.makeOverridable ({ rust, naersk ? naerskWithRust rust, ... } @ args: naersk.buildPackage ({
          buildInputs = with pkgs; [ ];
          targets = [ ];
          copyLibs = true;
          remapPathPrefix =
            true; # remove nix store references for a smaller output package
        } // args));

        project-rust = buildRustProject {
          root = ./.;
        };
        name = "Electrolysis";  # must match the name of the top-level .lean file
        project = leanPkgs.buildLeanPackage {
          inherit name;
          # deps = [ lean-ipld.project.${system} ];
          # Where the lean files are located
          src = ./src;
        };
        test = leanPkgs.buildLeanPackage {
          name = "Tests";
          deps = [ project ];
          # Where the lean files are located
          src = ./test;
        };
        joinDepsDerivations = getSubDrv:
          pkgs.lib.concatStringsSep ":" (map (d: "${getSubDrv d}") (project.allExternalDeps));
      in
      {
        inherit project test;
        packages = project // {
          ${name} = project.executable;
          inherit project-rust;
          test = test.executable;
        };

        defaultPackage = self.packages.${system}.${name};
        devShell = pkgs.mkShell {
          inputsFrom = [ project.executable ];
          buildInputs = with pkgs; [
            leanPkgs.lean-dev
            rust
            rust-analyzer
            clippy
            rustfmt
            emscripten
          ];
          LEAN_PATH = "./src:./test";
          LEAN_SRC_PATH = "./src:./test";
        };
      });
}
