import Mathlib.Data.Fintype.Powerset

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

end CorrelationGap
