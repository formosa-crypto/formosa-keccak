# Specification of the KECCAK algorithm (SHA-3 family)

This specfication is a translation to EasyCrypt of the *SHA-3
Standard: Permutation-Based Hash and Extendable-Output Functions*
[[FIPS-202]](https://csrc.nist.gov/publications/detail/fips/202/final).

The specification has been specialized for a *1600-bit width*
(**b=1600**), leading for the related quantities of **w=b/25=64** and
**l=log2(w)=6** (see Table 1 of [FIPS-202]).

The specification has been splited in the following files:
* **Keccak-p permutation** (Section 3 of [FIPS-202]) -- file
  `FIPS202_Keccakf1600.ec`
* **Keccak sponge construction and SHA-3 family of Hash function**
  (Sections 4, 5 and 6 of [FIPS-202]) -- file `FIPS202_SHA3.ec`

Furthermore, directory `./properties` include several general results
concerning the specification (e.g. equivalence wrt a full functional
specification, pre-computation of round-constants or rotation offsets,
etc.). Specifically, we provide the libraries:

* `./properties/Keccakf1600_Spec.ec` -- functional specification of
  keccak and corresponding correctness proof;
* `./properties/Keccak1600_Spec.ec` -- more convinient specification.

## Compiling the specification


The specification assumes the following entries on the EasyCrypt *loadpath*:
* *Jasmin* -- eclib Jasmin library;
* ~~ *JazzCommon* -- loadpath for required Jasmin's Array instances. ~~

These entries can either be specified on the command line (as is done
in this directory's `Makefile`), e.g.

```
easycrypt compile -I Jasmin:<path_to_jasmin>/eclib -I JazzCommon:<cryptospec_path/common> ...
```

or at the easycrypt's configuration file (usually, `~/.config/easycrypt/easycrypt.conf`)

```
[general]
idirs=Jasmin:<path_to_jasmin>/eclib
idirs=JazzCommon:<cryptospec_path>/common
```

