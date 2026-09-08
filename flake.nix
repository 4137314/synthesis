{
  description = "synthesis — Lean 4 multiphysics frontend development environment";
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
  outputs =
    { nixpkgs, ... }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = nixpkgs.lib.genAttrs systems;
    in
    {
      devShells = forAllSystems (
        system:
        let
          pkgs = import nixpkgs { inherit system; };
        in
        {
          default = pkgs.mkShell {
            # Lean module plugins resolve UnicodeBasic's C symbols lazily.
            # Eager binding breaks doc-gen4's pinned dependency on clean builds.
            hardeningDisable = [ "bindnow" ];
            packages = with pkgs; [
              elan
              git
              ripgrep
              nixfmt
              python3
            ];
            # Keep the downloaded compiler and Lake artifacts within the workspace.
            # Elan reads the exact compiler version from lean-toolchain.
            shellHook = ''
              export ELAN_HOME="$PWD/.elan"
              export PATH="$ELAN_HOME/bin:$PATH"
            '';
          };
        }
      );
      formatter = forAllSystems (system: nixpkgs.legacyPackages.${system}.nixfmt);
    };
}
