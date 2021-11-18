{ }:
let
  pkgs = import ./.ci/nixpkgs {};
  ghcs = [
    "ghc884"
    "ghc8107"
    "ghc901"
    "ghcjs"
    "ghcjs810"
  ];
in pkgs.lib.genAttrs ghcs (x: pkgs.haskell.packages.${x}.callCabal2nix "th-extras" ./. {})
