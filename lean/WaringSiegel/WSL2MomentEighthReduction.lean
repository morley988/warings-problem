import WaringSiegel.WSL2MomentMixed

/-!
# The genuine eighth-moment Cauchy and orthogonality reduction

The right hand side is a literal finite collision count. The shift aggregate
is kept nonnegative before the integral is expanded.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ComplexConjugate NumberField Classical

namespace WaringSiegel.WSL2

variable {G ι : Type*} [AddCommGroup G] [Fintype ι]

local instance eighthPeriodPositive : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
local instance eighthHaarProbability : IsProbabilityMeasure (latticeHaar (ι := ι)) := by
  unfold latticeHaar
  infer_instance

def correlationPairs (S H : Finset G) : Finset (Σ _ : G, G × G) :=
  H.sigma (fun h => (additiveOverlap S h).product (additiveOverlap S h))

def correlationFrequency (v : G → ι → ℤ) (q : Σ _ : G, G × G) : ι → ℤ :=
  (v (q.2.2 + q.1) - v q.2.2) - (v (q.2.1 + q.1) - v q.2.1)

def correlationAggregate (S H : Finset G) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) : ℝ :=
  ∑ h ∈ H, ‖finiteFrequencySum (additiveOverlap S h) (fun x => v (x+h) - v x) θ‖^2

theorem correlationAggregate_expansion (S H : Finset G) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    (correlationAggregate S H v θ : ℂ) =
      finiteFrequencySum (correlationPairs S H) (fun q => -correlationFrequency v q) θ := by
  unfold correlationAggregate finiteFrequencySum correlationPairs
  rw [Complex.ofReal_sum, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro h hh
  have heq := finiteFrequencySum_norm_sq_expansion (additiveOverlap S h)
    (fun x => v (x+h) - v x) θ
  dsimp [finiteFrequencySum] at heq
  rw [heq]
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  dsimp [correlationFrequency]
  abel

theorem fourth_le_correlationAggregate (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (v : G → ι → ℤ)
    (θ : ι → AddCircle (1 : ℝ)) :
    ‖finiteFrequencySum S v θ‖^4 ≤ (H.card : ℝ) * correlationAggregate S H v θ := by
  have h := finite_sum_fourth_le_correlations S H hH (fun x => latticeCharacter (v x) θ)
  simpa only [finiteFrequencySum, correlationAggregate, ← latticeCharacter_sub] using h

theorem integral_fourth_mul_correlation_count (S H : Finset G) (v : G → ι → ℤ) :
    (∫ θ, ‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ ∂latticeHaar) =
      (((((S.product S).product (S.product S)).product (correlationPairs S H)).filter
        (fun q => fourthFrequency v q.1 = correlationFrequency v q.2)).card : ℝ) := by
  have hexp (θ : ι → AddCircle (1 : ℝ)) :
      ((‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ : ℝ) : ℂ) =
      finiteFrequencySum (((S.product S).product (S.product S)).product (correlationPairs S H))
        (fun q => fourthFrequency v q.1 - correlationFrequency v q.2) θ := by
    rw [Complex.ofReal_mul, finiteFrequencySum_norm_fourth_expansion,
      correlationAggregate_expansion, finiteFrequencySum_mul]
    rfl
  calc
    (∫ θ, ‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ ∂latticeHaar) =
        (∫ θ, ((‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ : ℝ) : ℂ)
          ∂latticeHaar).re := by rw [integral_complex_ofReal]; rfl
    _ = _ := by
      simp_rw [hexp]
      rw [integral_finiteFrequencySum]
      simp only [sub_eq_zero, Complex.natCast_re]

theorem continuous_finiteFrequencySum (S : Finset G) (v : G → ι → ℤ) :
    Continuous (finiteFrequencySum S v) :=
  continuous_finset_sum _ (fun _ _ => continuous_latticeCharacter _)

theorem continuous_correlationAggregate (S H : Finset G) (v : G → ι → ℤ) :
    Continuous (correlationAggregate S H v) :=
  continuous_finset_sum _ (fun _ _ => (continuous_finiteFrequencySum _ _).norm.pow _)

/-- Closed analytic reduction of the actual eighth moment to the collision count. -/
theorem integral_eighth_le_collision_count (S H : Finset G)
    (hH : ∀ x ∈ S, ∀ y ∈ S, x-y ∈ H) (v : G → ι → ℤ) :
    (∫ θ, ‖finiteFrequencySum S v θ‖^8 ∂latticeHaar) ≤
      (H.card : ℝ) * (((((S.product S).product (S.product S)).product (correlationPairs S H)).filter
        (fun q => fourthFrequency v q.1 = correlationFrequency v q.2)).card : ℝ) := by
  have hi : Integrable (fun θ => ‖finiteFrequencySum S v θ‖^8) latticeHaar :=
    ((continuous_finiteFrequencySum S v).norm.pow _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hj : Integrable (fun θ => (H.card : ℝ) *
      (‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ)) latticeHaar :=
    (continuous_const.mul (((continuous_finiteFrequencySum S v).norm.pow _).mul
      (continuous_correlationAggregate S H v))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    (∫ θ, ‖finiteFrequencySum S v θ‖^8 ∂latticeHaar) ≤
        ∫ θ, (H.card : ℝ) * (‖finiteFrequencySum S v θ‖^4 * correlationAggregate S H v θ)
          ∂latticeHaar := by
      apply integral_mono hi hj
      intro θ
      have h := mul_le_mul_of_nonneg_left (fourth_le_correlationAggregate S H hH v θ)
        (show 0 ≤ ‖finiteFrequencySum S v θ‖^4 by positivity)
      nlinarith only [h]
    _ = _ := by rw [integral_const_mul, integral_fourth_mul_correlation_count]

end WaringSiegel.WSL2
