import Waring.SmoothMoments
import Waring.Orthogonality
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unconditional seed estimates for the actual smooth Weyl sums

The second moment is calculated exactly by Fourier orthogonality and the
injectivity of positive integer powers. The resulting full exponent one is
proved admissible with all quantifiers in `AdmissibleExponent` retained.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Waring.SmoothMoments

/-- The manuscript normalization of the phase agrees with mathlib's circle character. -/
theorem phase_eq_fourier (k n : ℕ) (α : ℝ) :
    phase k n α = fourier ((n ^ k : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) := by
  rw [phase, fourier_coe_apply]
  congr 1
  push_cast
  ring

/-- The zeroth moment is the length of the unit integration interval. -/
theorem smoothMoment_zero (k : ℕ) (P R : ℝ) : smoothMoment k 0 P R = 1 := by
  simp [smoothMoment]

/-- Exact second moment for every positive degree, all lengths and all smoothness cutoffs. -/
theorem smoothMoment_two_eq_card {k : ℕ} (hk : k ≠ 0) (P R : ℝ) :
    smoothMoment k 2 P R = ((smoothNumbers P R).card : ℝ) := by
  unfold smoothMoment smoothWeyl
  simp_rw [phase_eq_fourier]
  apply Waring.interval_integral_sq_norm_frequency_sum
  intro m n h
  change ((m ^ k : ℕ) : ℤ) = ((n ^ k : ℕ) : ℤ) at h
  have hpow : m ^ k = n ^ k := by exact_mod_cast h
  exact Nat.pow_left_injective hk hpow

/-- The exact second moment is at most the ambient length. -/
theorem smoothMoment_two_le {k : ℕ} (hk : k ≠ 0) {P : ℝ}
    (hP : 0 ≤ P) (R : ℝ) : smoothMoment k 2 P R ≤ P := by
  rw [smoothMoment_two_eq_card hk]
  calc
    ((smoothNumbers P R).card : ℝ) ≤ (⌊P⌋₊ : ℝ) := by
      exact_mod_cast smoothNumbers_card_le P R
    _ ≤ P := Nat.floor_le hP

/-- The full second-moment exponent one is admissible without any analytic hypothesis. -/
theorem admissibleExponent_two {k : ℕ} (hk : k ≠ 0) : AdmissibleExponent k 2 1 := by
  intro ε hε
  refine ⟨1, zero_lt_one, 1, zero_lt_one, 1, le_rfl, ?_⟩
  intro P hP R _hR _hRP
  calc
    smoothMoment k 2 P R ≤ P := smoothMoment_two_le hk (zero_le_one.trans hP) R
    _ = P ^ (1 : ℝ) := (Real.rpow_one P).symm
    _ ≤ 1 * P ^ (1 + ε) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le hP (le_add_of_nonneg_right hε.le)

/-- The zeroth seed is also an instance of the genuine admissibility definition. -/
theorem admissibleExponent_zero (k : ℕ) : AdmissibleExponent k 0 0 := by
  simpa using admissibleExponent_trivial k 0

end Waring.SmoothMoments
