import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pairwise-independent correlation-gap counterexample

This file starts a formalization of the five-element counterexample of
Ramachandra and Natarajan.  The first block defines the coverage function and
checks its elementary properties on the finite ground set.
-/

namespace CorrelationGap

abbrev Ground := Fin 5
abbrev Feature := Fin 4
abbrev Outcome := Finset Ground

/-- The features covered by ground-set element `i`. -/
def coveredBy (i : Ground) : Finset Feature :=
  match i with
  | 0 => {0, 1}
  | 1 => {0, 1, 2, 3}
  | 2 => {2, 3}
  | 3 => {0, 2}
  | 4 => {1, 3}

/-- The union of all features covered by a chosen outcome. -/
def coveredFeatures (S : Outcome) : Finset Feature :=
  S.biUnion coveredBy

/-- The concrete coverage function from the counterexample. -/
def coverage (S : Outcome) : ℕ :=
  (coveredFeatures S).card

/-- Monotonicity, specialized to functions on finite subsets. -/
def IsMonotone (f : Outcome → ℕ) : Prop :=
  ∀ S T, S ⊆ T → f S ≤ f T

/-- Submodularity in the union/intersection form. -/
def IsSubmodular (f : Outcome → ℕ) : Prop :=
  ∀ S T, f (S ∪ T) + f (S ∩ T) ≤ f S + f T

/-- An exact probability distribution on a finite type. -/
structure FiniteDistribution (α : Type*) [Fintype α] where
  weight : α → ℚ
  nonnegative : ∀ a, 0 ≤ weight a
  total : ∑ a, weight a = 1

namespace FiniteDistribution

/-- The exact expectation of a rational-valued function. -/
def expectation {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (f : α → ℚ) : ℚ :=
  ∑ a, μ.weight a * f a

end FiniteDistribution

theorem coverage_nonnegative (S : Outcome) : 0 ≤ coverage S :=
  Nat.zero_le _

theorem coverage_le_four (S : Outcome) : coverage S ≤ 4 := by
  simpa [coverage] using Finset.card_le_univ (coveredFeatures S)

theorem coverage_monotone : IsMonotone coverage := by
  unfold IsMonotone
  decide

theorem coverage_submodular : IsSubmodular coverage := by
  unfold IsSubmodular
  decide

/-- The three support outcomes of the numerator witness all cover every feature. -/
theorem witness_outcomes_cover_all :
    coverage {0, 2} = 4 ∧ coverage {1} = 4 ∧ coverage {3, 4} = 4 := by
  decide

/-! ## The unrestricted numerator witness -/

/-- The three atoms in the unrestricted witness distribution. -/
abbrev NumeratorAtom := Fin 3

/-- The outcome associated with each atom. -/
def numeratorOutcome (a : NumeratorAtom) : Outcome :=
  match a with
  | 0 => {0, 2}
  | 1 => {1}
  | 2 => {3, 4}

/-- The probability of each atom. -/
def numeratorWeight (a : NumeratorAtom) : ℚ :=
  match a with
  | 0 => 3 / 10
  | 1 => 7 / 20
  | 2 => 7 / 20

theorem numeratorWeight_nonnegative : ∀ a, 0 ≤ numeratorWeight a := by
  intro a
  fin_cases a <;> norm_num [numeratorWeight]

theorem numeratorWeight_total : ∑ a : NumeratorAtom, numeratorWeight a = 1 := by
  norm_num [Fin.sum_univ_succ, numeratorWeight]

/-- The unrestricted three-atom distribution attaining coverage four. -/
def numeratorDistribution : FiniteDistribution NumeratorAtom where
  weight := numeratorWeight
  nonnegative := numeratorWeight_nonnegative
  total := numeratorWeight_total

/-- The probability that ground-set element `i` belongs to the outcome. -/
def inclusionMarginal {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) (i : Ground) : ℚ :=
  ∑ a, if i ∈ X a then μ.weight a else 0

/-- The probability that both `i` and `j` belong to the outcome. -/
def jointInclusionMarginal {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) (i j : Ground) : ℚ :=
  ∑ a, if i ∈ X a ∧ j ∈ X a then μ.weight a else 0

/-- The exact expected coverage of a random outcome. -/
def expectedCoverage {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) : ℚ :=
  μ.expectation (fun a => coverage (X a))

/-- The inclusion marginals of `X` agree with `x`. -/
def HasMarginals {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) (x : Ground → ℚ) : Prop :=
  ∀ i, inclusionMarginal μ X i = x i

/-- Pairwise independence in the moment form used by the finite LP. -/
def IsPairwiseIndependent {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) : Prop :=
  ∀ i j, i ≠ j →
    jointInclusionMarginal μ X i j = inclusionMarginal μ X i * inclusionMarginal μ X j

/-- Feasibility for the pairwise-independent extension at marginal vector `x`. -/
def IsPairwiseFeasibleAt {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) (x : Ground → ℚ) : Prop :=
  HasMarginals μ X x ∧ IsPairwiseIndependent μ X

/-- The marginal vector used in the counterexample. -/
def targetMarginal (i : Ground) : ℚ :=
  match i with
  | 0 => 3 / 10
  | 1 => 7 / 20
  | 2 => 3 / 10
  | 3 => 7 / 20
  | 4 => 7 / 20

theorem numerator_marginals :
    ∀ i, inclusionMarginal numeratorDistribution numeratorOutcome i = targetMarginal i := by
  intro i
  fin_cases i <;>
    norm_num [inclusionMarginal, numeratorDistribution, numeratorOutcome,
      numeratorWeight, targetMarginal, Fin.sum_univ_succ, Fin.ext_iff]

theorem numerator_hasMarginals :
    HasMarginals numeratorDistribution numeratorOutcome targetMarginal :=
  numerator_marginals

/-- The numerator witness is unrestricted: coordinates `0` and `2` are not independent. -/
theorem numerator_not_pairwiseIndependent :
    ¬IsPairwiseIndependent numeratorDistribution numeratorOutcome := by
  intro h
  have h02 := h 0 2 (by decide)
  norm_num [jointInclusionMarginal, inclusionMarginal, numeratorDistribution,
    numeratorOutcome, numeratorWeight, Fin.sum_univ_succ, Fin.ext_iff] at h02

/-- Pairwise feasibility fixes every off-diagonal second moment. -/
theorem feasible_jointInclusionMarginal {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome)
    (h : IsPairwiseFeasibleAt μ X targetMarginal) {i j : Ground} (hij : i ≠ j) :
    jointInclusionMarginal μ X i j = targetMarginal i * targetMarginal j := by
  rw [h.2 i j hij, h.1 i, h.1 j]

theorem numerator_expectedCoverage :
    expectedCoverage numeratorDistribution numeratorOutcome = 4 := by
  have h₀ := witness_outcomes_cover_all.1
  have h₁ := witness_outcomes_cover_all.2.1
  have h₂ := witness_outcomes_cover_all.2.2
  norm_num [expectedCoverage, FiniteDistribution.expectation, numeratorDistribution, numeratorOutcome,
    numeratorWeight, Fin.sum_univ_succ, h₀, h₁, h₂]

end CorrelationGap
