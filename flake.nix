{
  description = "Rocq formalization of the Clarity language specification";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Exact toolchain versions. Evaluation fails if the locked nixpkgs
        # cannot provide them, so `nix flake update` never moves them silently.
        versions = {
          rocq = "9.3.0";
          stdlib = "9.2.0";
        };

        rocqPackages = pkgs.rocqPackages_9_3.overrideScope (
          self: super: {
            rocq-core = super.rocq-core.override { version = versions.rocq; };
            stdlib = super.stdlib.override { version = versions.stdlib; };
          }
        );
        rocqDeps = [
          rocqPackages.rocq-core
          rocqPackages.stdlib
        ];

        clarity-cert = pkgs.stdenv.mkDerivation {
          pname = "clarity-cert";
          version = "0.1.0";
          src = pkgs.lib.cleanSource ./.;

          nativeBuildInputs = rocqDeps ++ [ pkgs.gnumake ];

          buildPhase = ''
            runHook preBuild
            make -j$NIX_BUILD_CORES
            runHook postBuild
          '';

          installPhase = ''
            runHook preInstall
            mkdir -p $out/lib/rocq/user-contrib/ClarityCert
            cd theories
            find . -name '*.vo' -o -name '*.v' -o -name '*.glob' \
              | xargs -I{} install -Dm644 {} $out/lib/rocq/user-contrib/ClarityCert/{}
            runHook postInstall
          '';
        };
      in
      {
        packages.default = clarity-cert;

        # The pinned Rocq package set, for tooling built on top of this flake.
        legacyPackages.rocqPackages = rocqPackages;

        # `nix flake check` compiles every proof.
        checks.default = clarity-cert;

        devShells.default = pkgs.mkShell {
          packages = rocqDeps ++ [
            pkgs.gnumake
            pkgs.nixfmt
          ];
        };

        formatter = pkgs.nixfmt;
      }
    );
}
