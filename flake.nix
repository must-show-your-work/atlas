{
  description = "atlas -- Lean 4 library";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-parts.url = "github:hercules-ci/flake-parts";

    # lean4-nix: provides the Lean toolchain via Nix. Per ANG-611 / ANG-614
    # -- replaces the elan-with-FHS-binary pattern that doesn't work on
    # NixOS.
    lean4-nix = {
      url = "github:lenianiva/lean4-nix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  # Garnix binary cache: lean4-nix's CI publishes derivations here.
  # Kept even on the binary-toolchain path because lean4-nix evaluation
  # still pulls a few cached drvs from upstream. First `nix develop`
  # prompts for --accept-flake-config; one-time per project.
  nixConfig = {
    extra-substituters = [ "https://cache.garnix.io" ];
    extra-trusted-public-keys = [ "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g=" ];
  };

  outputs = { self, nixpkgs, lean4-nix, flake-parts, ... } @ inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-darwin" ];

      perSystem = { config, pkgs, system, ... }: let
        # ---- Lean toolchain (v4.30.0-rc2 binary via fetchBinaryLean) ----
        #
        # lean4-nix's public API doesn't export readBinaryToolchain (it's
        # defined in lib/overlay.nix but not inherited in the outputs).
        # Workaround: callPackage lib/toolchain.nix directly to access
        # fetchBinaryLean. That handles the upstream tarball fetch +
        # autoPatchelfHook (no nix-ld needed at runtime; the interpreter
        # is baked into the binary at install time).
        #
        # We use the binary path (not readRev source-build) for two
        # reasons:
        #  1) v4.30.0-rc2 is an RC, not in lean4-nix/manifests/, so the
        #     readRev source-build path hits a CMake permission error
        #     trying to configure_file into the read-only /nix/store
        #     lean source path.
        #  2) The binary tarball IS published by leanprover/lean4's CI
        #     for RC tags; autoPatchelfHook handles the FHS-to-NixOS
        #     interpreter rewiring.
        #
        # Bump when lean-toolchain pin changes: update tag + re-prefetch
        # hashes (`nix-prefetch-url <url>` then
        # `nix-hash --to-sri --type sha256 <base32>` to convert).
        leanToolchain = pkgs.callPackage "${lean4-nix.outPath}/lib/toolchain.nix" {};
        leanManifest = {
          tag = "v4.30.0-rc2";
          toolchain = {
            x86_64-linux = {
              url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-linux.tar.zst";
              hash = "sha256-W1FiXxVPChOze9iS8dlfeen9W58NCVtBJiFe4ryNvoY=";
            };
            aarch64-darwin = {
              url  = "https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-darwin_aarch64.tar.zst";
              hash = "sha256-aiPSYkH9eLzD0cJL6XNBv+P0Y18ub+q8u1hjA1KQqxs=";
            };
          };
        };
        leanBin = leanToolchain.fetchBinaryLean leanManifest;
        leanOverlay = final: prev: { lean = leanBin; };
        pkgsLean = import nixpkgs {
          inherit system;
          overlays = [ leanOverlay ];
        };
      in {
        devShells.default = pkgsLean.mkShell {
          name = "atlas lean shell";
          packages = [
            pkgsLean.lean
            pkgs.elan   # only for lake's manifest-update check; real lean is the Nix one
            pkgs.git
            pkgs.just
          ];
          shellHook = ''
            # ANG-642 defense: prepend the lean4-nix-built bin dir to PATH
            # so the lean4-elan-stub shipped by nixpkgs (and pulled into the
            # outer shell via the glamdring overlay from ANG-608 / PR #317)
            # cannot win on `command -v lean`. The stub's `readlink -f $0`
            # + PATH-strip self-loop fork-bombs when invoked from a nix-
            # develop context, pinning CPU with no output. Do NOT drop this
            # line on a "looks redundant" cleanup -- it's load-bearing
            # against the upstream stub bug.
            export PATH="${pkgsLean.lean}/bin:$PATH"

            # Workaround for nixpkgs #409490: `lake build` fails with the
            # default gcc linker on NixOS. Switch to clang.
            export LEAN_CC=clang
          '';
        };
      };
    };
}
