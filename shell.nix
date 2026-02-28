{ pkgs ?
    import (fetchTarball {
      url = "https://github.com/NixOS/nixpkgs/archive/c6f52ebd45e5925c188d1a20119978aa4ffd5ef6.tar.gz";
      sha256 = "sha256-m5KWt1nOm76ILk/JSCxBM4MfK3rYY7Wq9/TZIIeGnT8=";
    }) {}
, full ? true
}:

with pkgs;

let jasmin =
  jasmin-compiler.overrideAttrs (o: {
    src = fetchFromGitLab {
      owner = "jasmin-lang";
      repo = "jasmin-compiler";
      rev = "fe575eaf526e8f66bdae1854280b015c7fea1ed1";
      hash = "sha256-8xqanW1ay+BfXRWW1HFsdl5Grii0nTNugy2NxMseu1o=";
    };
  })
; in

let crypto-specs =
  fetchFromGitHub {
    owner = "formosa-crypto";
    repo = "crypto-specs";
    rev = "fb050598ed356c5c6604d92a1e198b2dd4543777";
    hash = "sha256-SG2jQzBcce/aPQAbJSVold2gm7buHOrOBsK7MHNIRFs=";
  }
; in

let
  oc = ocaml-ng.ocamlPackages_4_14;
  why = why3.override {
    ocamlPackages = oc;
    ideSupport = false;
    coqPackages = { coq = null; flocq = null; };
  };
  bitwuzla = callPackage ./config/bitwuzla.nix { inherit (oc) buildDunePackage zarith; };
  ecVersion = "5d4da0b5e935a01a598a93c84f31ddc1ec782f66";
  ec = (easycrypt.overrideAttrs (o: {
    src = fetchFromGitHub {
      owner = "vbgl";
      repo = "easycrypt";
      rev = ecVersion;
      hash = "sha256-5v5XgcPBI5wSXaxroNEtftwQV4TJmvBNoWcBjjnoFBc=";
    };
    postPatch = ''
      substituteInPlace dune-project \
        --replace-warn '(name easycrypt)' '(name easycrypt)(version ${ecVersion})'
    '';
    buildInputs = o.buildInputs ++ (with oc; [
      bitwuzla hex iter markdown progress ppx_deriving_yojson pcre2 tyxml
    ]);
  })).override {
    ocamlPackages = oc;
    why3 = why;
  };
in

let mkECvar = lib.strings.concatMapStringsSep ";" ({key, val}: "${key}:${val}"); in

mkShell ({
  JASMINC = "${jasmin.bin}/bin/jasminc";
  JASMINCT = "${jasmin.bin}/bin/jasmin-ct";
  JASMIN2EC = "${jasmin.bin}/bin/jasmin2ec";
  packages = [
    libxslt
    valgrind 
  ];
} // lib.optionalAttrs full {
  packages = [
    ec
    cvc5
    z3
  ];

  EC_RDIRS = mkECvar [
    { key = "Jasmin"; val = "${jasmin.lib}/lib/easycrypt/jasmin"; }
    { key = "CryptoSpecs"; val = "${crypto-specs}/fips202"; }
  ];
  EC_IDIRS = mkECvar [
    { key = "JazzEC"; val = "${crypto-specs}/arrays"; }
    { key = "JazzEC"; val = "${crypto-specs}/common"; }
    { key = "CryptoSpecs"; val = "${crypto-specs}/arrays"; }
    { key = "CryptoSpecs"; val = "${crypto-specs}/common"; }
  ];
})
