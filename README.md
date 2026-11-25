# The Exact Logical Strength of the Downward Löwenheim-Skolem Theorem Formalised in Rocq

## Content

The Rocq code is in the [theories](theories) folder. Output of coqdoc is available under [website](website).

Material in the `Core` folder is from the [first-order logic library](https://github.com/uds-psl/coq-library-fol), trimmed to the bare necessity to quicken compilation time.

Our proof is contained in the `DLS` folder.

- `Defs.v` contains most definitions used, including the statement of the DLS theorem
- `LogicalPrinciples.v` contains proofs of impications between blurred and non-blurred logical principles
- `Retracts.v` contains the machinery used for size copmarisons, mainly instances definitions
- `Utils.v` contains various helper lemmas
- `Signatures.v` contains the proofs that if a signature is *small*, then the associated types of terms and formulas are both *small* (it throwing 2 compilation warnings is expected)
- `SubsetsDefs.v` defines subsets according to the chosen reprentation and proves some of their properties
- `DLSfw.v` is the forward direction of the equivalence, using the main statement of DLS
- `DLSalt.v` proves the equivalence between both statements of DLS, main and alternate one
- `DLSbw.v` is the backward direction of the equivalence, using the alternate statement of DLS
- `ReverseAnalysisDLS.v` wraps up everything into a main theorem (and checks that no additional hypotheses are used) and also contains a proof that we generalise Kirst and Zeng's result.

## Installation

Run the following commands when at the root of the repo:

```
opam switch create . 5.4.0 --deps-only --repos=default,rocq-released=https://rocq-prover.org/opam/released
eval $(opam env)
make
```

## Article's authors

- Yannick Forster
- Sam van Gool
- Timothée Huneau
- Dominik Kirst