import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

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

@[simp]
theorem expectation_const {α : Type*} [Fintype α] (μ : FiniteDistribution α) (c : ℚ) :
    μ.expectation (fun _ => c) = c := by
  rw [expectation, ← Finset.sum_mul, μ.total, one_mul]

@[simp]
theorem expectation_add {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (f g : α → ℚ) :
    μ.expectation (fun a => f a + g a) = μ.expectation f + μ.expectation g := by
  simp [expectation, mul_add, Finset.sum_add_distrib]

@[simp]
theorem expectation_sub {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (f g : α → ℚ) :
    μ.expectation (fun a => f a - g a) = μ.expectation f - μ.expectation g := by
  simp [expectation, mul_sub, Finset.sum_sub_distrib]

@[simp]
theorem expectation_const_mul {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (c : ℚ) (f : α → ℚ) :
    μ.expectation (fun a => c * f a) = c * μ.expectation f := by
  simp only [expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

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

/-- The rational indicator that `i` belongs to `S`. -/
def inclusionIndicator (i : Ground) (S : Outcome) : ℚ :=
  if i ∈ S then 1 else 0

@[simp]
theorem expectation_inclusionIndicator {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome) (i : Ground) :
    μ.expectation (fun a => inclusionIndicator i (X a)) = inclusionMarginal μ X i := by
  unfold FiniteDistribution.expectation inclusionMarginal inclusionIndicator
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : i ∈ X a <;> simp [h]

@[simp]
theorem expectation_indicator_mul {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome) (i j : Ground) :
    μ.expectation (fun a => inclusionIndicator i (X a) * inclusionIndicator j (X a)) =
      jointInclusionMarginal μ X i j := by
  unfold FiniteDistribution.expectation jointInclusionMarginal inclusionIndicator
  apply Finset.sum_congr rfl
  intro a _
  by_cases hi : i ∈ X a <;> by_cases hj : j ∈ X a <;> simp [hi, hj]

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

/-! ## A nonempty pairwise-feasible family -/

/-- Target marginal numerators over the common denominator twenty. -/
def targetCount (i : Ground) : ℕ :=
  match i with
  | 0 => 6
  | 1 => 7
  | 2 => 6
  | 3 => 7
  | 4 => 7

def productDenominator : ℕ := 20 ^ 5

/-- Integer numerator of the mutually independent product mass on `S`. -/
def productWeightNumerator (S : Outcome) : ℕ :=
  ∏ i : Ground, if i ∈ S then targetCount i else 20 - targetCount i

theorem productWeightNumerator_total :
    ∑ S : Outcome, productWeightNumerator S = productDenominator := by
  decide

theorem productWeightNumerator_marginal :
    ∀ i, (∑ S : Outcome, if i ∈ S then productWeightNumerator S else 0) =
      targetCount i * 20 ^ 4 := by
  decide

theorem productWeightNumerator_pair :
    ∀ i j, i ≠ j →
      (∑ S : Outcome, if i ∈ S ∧ j ∈ S then productWeightNumerator S else 0) =
        targetCount i * targetCount j * 20 ^ 3 := by
  decide

/-- Mutually independent product mass, represented exactly over `ℚ`. -/
def productWeight (S : Outcome) : ℚ :=
  productWeightNumerator S / productDenominator

theorem sum_natCast_div (f : Outcome → ℕ) (d : ℕ) :
    (∑ S : Outcome, (f S : ℚ) / d) = ((∑ S : Outcome, f S : ℕ) : ℚ) / d := by
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul]
  simp

theorem productWeight_event (P : Outcome → Prop) [DecidablePred P] :
    (∑ S : Outcome, if P S then productWeight S else 0) =
      ((∑ S : Outcome, if P S then productWeightNumerator S else 0 : ℕ) : ℚ) /
        productDenominator := by
  calc
    (∑ S : Outcome, if P S then productWeight S else 0) =
        ∑ S : Outcome,
          ((if P S then productWeightNumerator S else 0 : ℕ) : ℚ) / productDenominator := by
            apply Finset.sum_congr rfl
            intro S _
            by_cases h : P S <;> simp [h, productWeight]
    _ = ((∑ S : Outcome, if P S then productWeightNumerator S else 0 : ℕ) : ℚ) /
          productDenominator := sum_natCast_div _ _

theorem productWeight_nonnegative : ∀ S, 0 ≤ productWeight S := by
  intro S
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem productWeight_total : ∑ S : Outcome, productWeight S = 1 := by
  calc
    (∑ S : Outcome, productWeight S) =
        ((∑ S : Outcome, productWeightNumerator S : ℕ) : ℚ) / productDenominator :=
      sum_natCast_div _ _
    _ = 1 := by rw [productWeightNumerator_total]; norm_num [productDenominator]

/-- The ordinary independent product distribution at the target marginals. -/
def productDistribution : FiniteDistribution Outcome where
  weight := productWeight
  nonnegative := productWeight_nonnegative
  total := productWeight_total

theorem productDistribution_hasMarginals :
    HasMarginals productDistribution id targetMarginal := by
  intro i
  change (∑ S : Outcome, if i ∈ S then productWeight S else 0) = targetMarginal i
  rw [productWeight_event (fun S => i ∈ S)]
  rw [productWeightNumerator_marginal i]
  fin_cases i <;> norm_num [targetCount, targetMarginal, productDenominator]

theorem productDistribution_pairMoment (i j : Ground) (hij : i ≠ j) :
    jointInclusionMarginal productDistribution id i j = targetMarginal i * targetMarginal j := by
  change (∑ S : Outcome, if i ∈ S ∧ j ∈ S then productWeight S else 0) =
    targetMarginal i * targetMarginal j
  rw [productWeight_event (fun S => i ∈ S ∧ j ∈ S)]
  rw [productWeightNumerator_pair i j hij]
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | norm_num [targetCount, targetMarginal, productDenominator]

theorem productDistribution_pairwiseIndependent :
    IsPairwiseIndependent productDistribution id := by
  intro i j hij
  rw [productDistribution_pairMoment i j hij]
  rw [productDistribution_hasMarginals i, productDistribution_hasMarginals j]

theorem productDistribution_pairwiseFeasible :
    IsPairwiseFeasibleAt productDistribution id targetMarginal :=
  ⟨productDistribution_hasMarginals, productDistribution_pairwiseIndependent⟩

/-! ## The quadratic dual certificate -/

/-- Integer-valued membership indicator used for exhaustive checking. -/
def inclusionIndicatorInt (i : Ground) (S : Outcome) : ℤ :=
  if i ∈ S then 1 else 0

/-- Twice the quadratic dual certificate, with integral coefficients. -/
def dualCertificateTwiceInt (S : Outcome) : ℤ :=
  let I := fun i => inclusionIndicatorInt i S
  1 + 3 * (I 0 + I 2 + I 3 + I 4) + 7 * I 1
    - 2 * (I 0 * I 1 + I 1 * I 2)
    - 3 * (I 1 * I 3 + I 1 * I 4)
    + (I 0 * I 2 + I 3 * I 4)
    - (I 0 * I 3 + I 0 * I 4 + I 2 * I 3 + I 2 * I 4)

/-- Rational form of twice the quadratic dual certificate. -/
def dualCertificateTwice (S : Outcome) : ℚ :=
  let I := fun i => inclusionIndicator i S
  1 + 3 * (I 0 + I 2 + I 3 + I 4) + 7 * I 1
    - 2 * (I 0 * I 1 + I 1 * I 2)
    - 3 * (I 1 * I 3 + I 1 * I 4)
    + (I 0 * I 2 + I 3 * I 4)
    - (I 0 * I 3 + I 0 * I 4 + I 2 * I 3 + I 2 * I 4)

/-- The quadratic certificate itself. -/
def dualCertificate (S : Outcome) : ℚ :=
  dualCertificateTwice S / 2

/-- The moment expression obtained by taking the expectation of the doubled certificate. -/
def dualMomentValue {α : Type*} [Fintype α] (μ : FiniteDistribution α)
    (X : α → Outcome) : ℚ :=
  let m := inclusionMarginal μ X
  let p := jointInclusionMarginal μ X
  1 + 3 * (m 0 + m 2 + m 3 + m 4) + 7 * m 1
    - 2 * (p 0 1 + p 1 2)
    - 3 * (p 1 3 + p 1 4)
    + (p 0 2 + p 3 4)
    - (p 0 3 + p 0 4 + p 2 3 + p 2 4)

theorem dualCertificateTwiceInt_dominates :
    ∀ S, (2 : ℤ) * coverage S ≤ dualCertificateTwiceInt S := by
  decide

theorem dualCertificateTwice_eq_cast (S : Outcome) :
    dualCertificateTwice S = (dualCertificateTwiceInt S : ℚ) := by
  simp [dualCertificateTwice, dualCertificateTwiceInt, inclusionIndicator,
    inclusionIndicatorInt]

theorem coverage_le_dualCertificate (S : Outcome) :
    (coverage S : ℚ) ≤ dualCertificate S := by
  rw [dualCertificate]
  apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 2)).2
  have h := dualCertificateTwiceInt_dominates S
  have h' : ((((2 : ℤ) * (coverage S : ℤ)) : ℤ) : ℚ) ≤
      (dualCertificateTwiceInt S : ℚ) :=
    Int.cast_le.2 h
  simpa [dualCertificateTwice_eq_cast, mul_comm] using h'

theorem expectation_dualCertificateTwice {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome) :
    μ.expectation (fun a => dualCertificateTwice (X a)) = dualMomentValue μ X := by
  simp [dualCertificateTwice, dualMomentValue]

theorem dualMomentValue_of_feasible {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome)
    (h : IsPairwiseFeasibleAt μ X targetMarginal) :
    dualMomentValue μ X = 479 / 80 := by
  dsimp [dualMomentValue]
  rw [h.1 0, h.1 1, h.1 2, h.1 3, h.1 4]
  rw [feasible_jointInclusionMarginal μ X h (i := 0) (j := 1) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 1) (j := 2) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 1) (j := 3) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 1) (j := 4) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 0) (j := 2) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 3) (j := 4) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 0) (j := 3) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 0) (j := 4) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 2) (j := 3) (by decide)]
  rw [feasible_jointInclusionMarginal μ X h (i := 2) (j := 4) (by decide)]
  norm_num [targetMarginal]

theorem expectation_dualCertificate_of_feasible {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome)
    (h : IsPairwiseFeasibleAt μ X targetMarginal) :
    μ.expectation (fun a => dualCertificate (X a)) = 479 / 160 := by
  calc
    μ.expectation (fun a => dualCertificate (X a)) =
        μ.expectation (fun a => (1 / 2 : ℚ) * dualCertificateTwice (X a)) := by
          congr 1
          funext a
          unfold dualCertificate
          ring
    _ = (1 / 2 : ℚ) * μ.expectation (fun a => dualCertificateTwice (X a)) := by
      rw [FiniteDistribution.expectation_const_mul]
    _ = (1 / 2 : ℚ) * dualMomentValue μ X := by
      rw [expectation_dualCertificateTwice]
    _ = 479 / 160 := by
      rw [dualMomentValue_of_feasible μ X h]
      norm_num

theorem expectedCoverage_le_expectation_dualCertificate {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome) :
    expectedCoverage μ X ≤ μ.expectation (fun a => dualCertificate (X a)) := by
  unfold expectedCoverage FiniteDistribution.expectation
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (coverage_le_dualCertificate (X a)) (μ.nonnegative a)

/-- Universal upper bound for the pairwise-independent denominator. -/
theorem pairwise_expectedCoverage_le {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome)
    (h : IsPairwiseFeasibleAt μ X targetMarginal) :
    expectedCoverage μ X ≤ 479 / 160 := by
  calc
    expectedCoverage μ X ≤ μ.expectation (fun a => dualCertificate (X a)) :=
      expectedCoverage_le_expectation_dualCertificate μ X
    _ = 479 / 160 := expectation_dualCertificate_of_feasible μ X h

/-- No distribution can exceed the four available features. -/
theorem expectedCoverage_le_four {α : Type*} [Fintype α]
    (μ : FiniteDistribution α) (X : α → Outcome) :
    expectedCoverage μ X ≤ 4 := by
  unfold expectedCoverage FiniteDistribution.expectation
  calc
    (∑ a, μ.weight a * (coverage (X a) : ℚ)) ≤ ∑ a, μ.weight a * 4 := by
      apply Finset.sum_le_sum
      intro a _
      apply mul_le_mul_of_nonneg_left
      · exact Nat.cast_le.2 (coverage_le_four (X a))
      · exact μ.nonnegative a
    _ = 4 := by rw [← Finset.sum_mul, μ.total]; norm_num

theorem numerator_expectedCoverage :
    expectedCoverage numeratorDistribution numeratorOutcome = 4 := by
  have h₀ := witness_outcomes_cover_all.1
  have h₁ := witness_outcomes_cover_all.2.1
  have h₂ := witness_outcomes_cover_all.2.2
  norm_num [expectedCoverage, FiniteDistribution.expectation, numeratorDistribution, numeratorOutcome,
    numeratorWeight, Fin.sum_univ_succ, h₀, h₁, h₂]

theorem certified_ratio :
    (4 : ℚ) / (479 / 160) = 640 / 479 ∧ (4 / 3 : ℚ) < 640 / 479 := by
  norm_num

/-- End-to-end certificate for the Ramachandra--Natarajan counterexample. -/
theorem pairwise_correlation_gap_counterexample :
    HasMarginals numeratorDistribution numeratorOutcome targetMarginal ∧
    expectedCoverage numeratorDistribution numeratorOutcome = 4 ∧
    (∀ μ : FiniteDistribution Outcome, expectedCoverage μ id ≤ 4) ∧
    IsPairwiseFeasibleAt productDistribution id targetMarginal ∧
    (∀ μ : FiniteDistribution Outcome,
      IsPairwiseFeasibleAt μ id targetMarginal → expectedCoverage μ id ≤ 479 / 160) ∧
    (4 : ℚ) / (479 / 160) = 640 / 479 ∧
    (4 / 3 : ℚ) < 640 / 479 := by
  refine ⟨numerator_hasMarginals, numerator_expectedCoverage, ?_,
    productDistribution_pairwiseFeasible, ?_, certified_ratio.1, certified_ratio.2⟩
  · intro μ
    exact expectedCoverage_le_four μ id
  · intro μ h
    exact pairwise_expectedCoverage_le μ id h

end CorrelationGap
