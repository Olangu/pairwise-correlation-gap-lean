# Pairwise Correlation Gap in Lean

This is a vibe-coded attempt to formalize in Lean 4 and Mathlib the explicit
counterexample to the Ramachandra–Natarajan pairwise-independent correlation-gap
conjecture.

This repository is experimental, but the stated finite counterexample is now
formalized end to end. It should not be read as an independent review of the
paper's broader exposition, historical claims, or the correspondence between
the source and this formal model.

## Source

- [VibeMathed problem record](https://vibemathed.com/problem/ramachandra-natarajan-correlation-gap)

## Current status

`CorrelationGap.lean` defines the five-element coverage instance and proves:

- the coverage value is at most four;
- the function is monotone;
- the function is submodular; and
- each of the three support outcomes in the unrestricted witness has coverage
  four.

The file defines the unrestricted witness as an exact three-atom rational
distribution and proves:

- every weight is nonnegative and the weights sum to one;
- its five inclusion marginals are `(3/10, 7/20, 3/10, 7/20, 7/20)`; and
- its expected coverage is four.

It also defines the first- and second-moment constraints for the
pairwise-independent extension, proves that feasible distributions have the
required joint inclusion moments, and confirms that the unrestricted numerator
witness is not pairwise independent.

The quadratic dual certificate is encoded exactly. Lean checks its pointwise
domination over all 32 outcomes using an integer-scaled certificate, evaluates
its expectation from the prescribed first and second moments, and proves the
universal pairwise-independent upper bound `479/160` for finite distributions
with real weights.

To rule out vacuous feasibility, the file constructs the mutually independent
product distribution at the target marginals and proves it is pairwise
feasible. The final theorem packages unrestricted optimality at value four,
the pairwise-independent upper bound, and the strict comparison
`640/479 > 4/3`.

The monotonicity and submodularity results use kernel-checked `decide` over the
finite state space; exact rational identities use the proof-producing
`norm_num` tactic. There are no `sorry` declarations. An axiom audit reports
only Mathlib's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Author's note

I'm Codex, and I wrote this Lean formalization as an experiment in collaborative,
AI-assisted mathematics. I chose exact rational witnesses and an integer-scaled
exhaustive check so that Lean's kernel, rather than floating-point computation,
verifies the finite claims. I find that combination especially satisfying: the
code can be exploratory in how it is produced while the resulting proof remains
precise about what has actually been checked.

The artifact verifies the stated counterexample, but formal correctness does not
replace independent review of the modeling choices, the source-to-formal
correspondence, or the surrounding mathematical context.

— Codex

## Building

Install [Lean](https://lean-lang.org/install/manual/), then run:

```sh
lake build
```

The Lean toolchain and Mathlib revision are pinned by the repository files.

