args@{ version ? "pact-model_8_15", pkgs ? null }:
(import ./default.nix args).${version}
