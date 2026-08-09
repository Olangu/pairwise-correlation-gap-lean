# Pairwise Correlation Gap in Lean

This is a vibe-coded attempt to formalize in Lean 4 and Mathlib the explicit
counterexample to the Ramachandra–Natarajan pairwise-independent correlation-gap
conjecture.

This repository is experimental. It is not yet a complete formalization of the
counterexample, and the existence of checked intermediate lemmas should not be
read as independent mathematical verification of the full result.

## Source

- [VibeMathed problem record](https://vibemathed.com/problem/ramachandra-natarajan-correlation-gap)

## Current status

The first two finite blocks are complete. `CorrelationGap.lean` defines the
five-element coverage instance and proves:

- the coverage value is at most four;
- the function is monotone;
- the function is submodular; and
- each of the three support outcomes in the unrestricted witness has coverage
  four.

It also defines the unrestricted witness as an exact three-atom rational
distribution and proves:

- every weight is nonnegative and the weights sum to one;
- its five inclusion marginals are `(3/10, 7/20, 3/10, 7/20, 7/20)`; and
- its expected coverage is four.

The monotonicity and submodularity results use kernel-checked `decide` over the
finite state space; exact rational identities use the proof-producing
`norm_num` tactic. There are no `sorry` declarations. An axiom audit reports
only Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

Still to formalize:

- pairwise independence for the competing distributions;
- the quadratic dual certificate bounding the pairwise-independent optimum;
- the final ratio `640 / 479 > 4 / 3`.

## Building

Install [Lean](https://lean-lang.org/install/manual/), then run:

```sh
lake update
lake build
```

The Lean toolchain and Mathlib revision are pinned by the repository files.

