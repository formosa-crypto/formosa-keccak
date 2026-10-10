{ pkgs ?
    import (fetchTarball {
      # nixos-26.05
      url = "https://github.com/NixOS/nixpkgs/archive/2efa67fd26b6df417c33e4603185c701f260dd83.tar.gz";
      sha256 = "sha256-v72qr4LsSz61tQki/41nHKZKPY6NSeZavtGlAInOCng=";
    }) {}
, full ? true
}:

with pkgs;

# Jasmin snapshot of branch safety-assert2 (85234091), not a release: its
# eclib has JSafety (needed by proof/amd64/safety; no release up to 2026.09.0
# ships it) and the VPSLL/VPSRL semantics the proofs are checked against. Its
# jasmin2ec output matches the committed models (extracted with 2026.03.1)
# up to whitespace.
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
  # EasyCrypt main needs OCaml >= 5.1 (Mutex.protect) and
  # warns against the GC regression of 5.0-5.3; the default set of
  # nixos-26.05 (5.4.1) is binary-cached. bitwuzla-cxx 0.9.0 (the opam
  # version) instead of nixpkgs' 0.8.2: with 0.8.2 the circuit-based proofs
  # (e.g. ref/Keccakf1600_opt.ec) take over an hour and >12 GB.
  oc = ocamlPackages.overrideScope (_: super: {
    bitwuzla-cxx = super.bitwuzla-cxx.overrideAttrs (o: rec {
      version = "0.9.0";
      name = "ocaml${super.ocaml.version}-bitwuzla-cxx-${version}";
      src = fetchurl {
        url = "https://github.com/bitwuzla/ocaml-bitwuzla/releases/download/${version}/bitwuzla-cxx-${version}.tbz";
        hash = "sha256-pKTNDmXkL5N6E2jkZyjRX5PzMZ3qeSyCZfdGW3I9dYY=";
      };
      # 0.9 links GMP and MPFR, which its dune files look for in Homebrew
      postPatch = ''
        substituteInPlace dune api/dune vendor/dune \
          --replace-quiet '-I/opt/homebrew/include' "" \
          --replace-quiet '-L/opt/homebrew/lib' ""
      '';
      propagatedBuildInputs = o.propagatedBuildInputs ++ [ gmp mpfr ];
    });
  });
  why = why3.override {
    ocamlPackages = oc;
    ideSupport = false;
    coqPackages = { coq = null; flocq = null; };
  };
  # EasyCrypt main, following its HEAD: fetchGit resolves the branch at
  # evaluation time (cached by nix for tarball-ttl, 1h by default), so there is
  # no rev/hash to bump. For a reproducible build pin a commit instead:
  #   ecSrc = builtins.fetchGit { url = ...; rev = "<commit>"; };
  ecSrc = builtins.fetchGit {
    url = "https://github.com/EasyCrypt/easycrypt.git";
    ref = "main";
  };
  ecVersion = ecSrc.rev;
  ec = (easycrypt.overrideAttrs (o: {
    src = ecSrc;
    postPatch = ''
      substituteInPlace dune-project \
        --replace-warn '(name easycrypt)' '(name easycrypt)(version ${ecVersion})'
    '';
    buildInputs = o.buildInputs ++ (with oc; [
      bitwuzla-cxx hex iter markdown progress ppx_deriving_yojson pcre2 tyxml
    ]);
  })).override {
    ocamlPackages = oc;
    why3 = why;
  };
  # proof/easycrypt.project asks for Z3@4.13 and CVC5@1.3. These are lower
  # bounds (EasyCrypt picks the oldest installed version >= the pin), and
  # why3config must recognise the provers' version. Use the versions the smt
  # calls were tuned with, Z3 4.13.4 and CVC5 1.3.2, from older nixpkgs
  # releases (binary-cached for Linux and macOS): nixos-26.05 has Z3 4.16,
  # and its CVC5 1.3.4 prints a version string Why3 1.8.2 does not recognise.
  pinnedPkgs = rev: sha256: import (fetchTarball {
    url = "https://github.com/NixOS/nixpkgs/archive/${rev}.tar.gz";
    inherit sha256;
  }) { inherit (stdenv.hostPlatform) system; };
  z3_4_13 = (pinnedPkgs # nixos-24.11
    "50ab793786d9de88ee30ec4e4c24fb4236fc2674"
    "sha256-/bVBlRpECLVzjV19t5KMdMFWSwKLtb5RyXdjz3LJT+g=").z3_4_13;
  cvc5_1_3 = (pinnedPkgs # nixos-25.11
    "b6018f87da91d19d0ab4cf979885689b469cdd41"
    "sha256-twXPFqFsrrY5r28Zh7Homgcp2gUMBgQ6WDS98Q/3xFI=").cvc5;
in

let mkECvar = lib.strings.concatMapStringsSep ";" ({key, val}: "${key}:${val}"); in

mkShell ({
  JASMINC = "${jasmin.bin}/bin/jasminc";
  JASMINCT = "${jasmin.bin}/bin/jasmin-ct";
  JASMIN2EC = "${jasmin.bin}/bin/jasmin2ec";
  packages = [
    libxslt
  ] ++ lib.optionals stdenv.isLinux [
    valgrind
  ] ++ lib.optionals full [
    ec
    cvc5_1_3
    z3_4_13
  ];
} // lib.optionalAttrs full {
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
