{
  description = "atlas -- Lean 4 library";

  inputs = {
    # Host-specific absolute path: nix can't follow `path:../shed` once
    # this tree is copied into /nix/store. Long-term, publish shed.
    shed.url = "path:/storage/code/must-show-your-work/shed";
    nixpkgs.follows = "shed/nixpkgs";
    flake-parts.follows = "shed/flake-parts";
  };

  nixConfig = {
    extra-substituters = [ "https://cache.garnix.io" ];
    extra-trusted-public-keys = [ "cache.garnix.io:CTFPyKSLcx5RMJKfLo5EEPUObbA78b0YQ2DTCJXqr9g=" ];
  };

  outputs = { self, nixpkgs, flake-parts, shed, ... } @ inputs:
    flake-parts.lib.mkFlake { inherit inputs; } {
      systems = [ "x86_64-linux" "aarch64-darwin" ];

      perSystem = { config, pkgs, system, ... }: {
        devShells.default = shed.lib.mkLeanShell {
          inherit pkgs system;
          name = "atlas lean shell";

          # Bump when ./lean-toolchain changes: refetch with
          #   nix store prefetch-file --hash-type sha256 <url>
          manifest = {
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
        };
      };
    };
}
