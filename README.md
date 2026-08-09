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

Finally, it defines the first- and second-moment constraints for the
pairwise-independent extension, proves that feasible distributions have the
required joint inclusion moments, and confirms that the unrestricted numerator
witness is not pairwise independent.

The quadratic dual certificate is encoded exactly. Lean checks its pointwise
domination over all 32 outcomes using an integer-scaled certificate, evaluates
its expectation from the prescribed first and second moments, and proves the
universal pairwise-independent upper bound `479/160`.

To rule out vacuous feasibility, the file constructs the mutually independent
product distribution at the target marginals and proves it is pairwise
feasible. The final theorem packages unrestricted optimality at value four,
the pairwise-independent upper bound, and the strict comparison
`640/479 > 4/3`.

The monotonicity and submodularity results use kernel-checked `decide` over the
finite state space; exact rational identities use the proof-producing
`norm_num` tactic. There are no `sorry` declarations. An axiom audit reports
only Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

The finite counterexample is now formalized end to end. This does not constitute
an independent review of the paper's broader exposition or historical claims.

## Building

Install [Lean](https://lean-lang.org/install/manual/), then run:

```sh
lake update
lake build
```

The Lean toolchain and Mathlib revision are pinned by the repository files.

