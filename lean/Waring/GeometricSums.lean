import Waring.Orthogonality
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite geometric character sums

The phase is the actual standard character `exp(2 pi i alpha)` from mathlib.
The reciprocal-distance bound includes a separate integer branch so that
Lean's convention `0⁻¹ = 0` never creates a false bound at integral phases.
-/

noncomputable section

open scoped BigOperators

namespace Waring

/-- The distance to the nearest integer. -/
def integerDistance (α : ℝ) : ℝ := |α - (round α : ℝ)|

/-- The unit-frequency character of a real phase. -/
def unitCharacter (α : ℝ) : ℂ := fourier 1 (α : AddCircle (1 : ℝ))

/-- A finite linear Weyl sum starting with frequency zero. -/
def linearWeylSum (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, fourier (n : ℤ) (α : AddCircle (1 : ℝ))

/-- The corresponding finite sum with an arbitrary integer starting frequency. -/
def shiftedLinearWeylSum (M : ℤ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ Finset.range N, fourier ((n : ℤ) + M) (α : AddCircle (1 : ℝ))

/-- Adapter from the usual real linear phase to the additive-circle character. -/
theorem exp_linear_eq_fourier (α : ℝ) (m : ℤ) :
    Complex.exp (((2 * Real.pi * (α * (m : ℝ)) : ℝ) : ℂ) * Complex.I) =
      fourier m (α : AddCircle (1 : ℝ)) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

theorem norm_fourier_value {T : ℝ} (m : ℤ) (x : AddCircle T) : ‖fourier m x‖ = 1 := by
  exact Circle.norm_coe _

theorem norm_unitCharacter (α : ℝ) : ‖unitCharacter α‖ = 1 :=
  norm_fourier_value _ _

theorem fourier_nat_eq_pow {T : ℝ} (n : ℕ) (x : AddCircle T) :
    fourier (n : ℤ) x = fourier 1 x ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, fourier_add, ih, pow_succ]

theorem linearWeylSum_eq_geometric (N : ℕ) (α : ℝ) :
    linearWeylSum N α = ∑ n ∈ Finset.range N, unitCharacter α ^ n := by
  unfold linearWeylSum unitCharacter
  simp_rw [fourier_nat_eq_pow]

theorem norm_linearWeylSum_le_length (N : ℕ) (α : ℝ) :
    ‖linearWeylSum N α‖ ≤ (N : ℝ) := by
  unfold linearWeylSum
  calc
    ‖∑ n ∈ Finset.range N, fourier (n : ℤ) (α : AddCircle (1 : ℝ))‖ ≤
        ∑ n ∈ Finset.range N, ‖fourier (n : ℤ) (α : AddCircle (1 : ℝ))‖ := norm_sum_le _ _
    _ = (N : ℝ) := by simp

/-- Exact geometric summation and the triangle inequality give the chord-distance bound. -/
theorem norm_linearWeylSum_le_chord (N : ℕ) (α : ℝ) (hα : unitCharacter α ≠ 1) :
    ‖linearWeylSum N α‖ ≤ 2 / ‖unitCharacter α - 1‖ := by
  rw [linearWeylSum_eq_geometric, geom_sum_eq hα, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖unitCharacter α ^ N - 1‖ ≤ ‖unitCharacter α ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [norm_pow, norm_unitCharacter]

/-- The chord of a unit complex exponential has the usual half-angle length. -/
theorem norm_exp_two_mul_I_sub_one (t : ℝ) :
    ‖Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin t| := by
  have hdouble : (((2 * t : ℝ) : ℂ) * Complex.I) =
      (t : ℂ) * Complex.I + (t : ℂ) * Complex.I := by push_cast; ring
  have hcancel : (t : ℂ) * Complex.I + (-(t : ℂ)) * Complex.I = 0 := by ring
  have hunit : Complex.exp ((t : ℂ) * Complex.I) *
      Complex.exp ((-(t : ℂ)) * Complex.I) = 1 := by
    rw [← Complex.exp_add, hcancel, Complex.exp_zero]
  have hdiff : Complex.exp ((t : ℂ) * Complex.I) -
      Complex.exp ((-(t : ℂ)) * Complex.I) = 2 * (Real.sin t : ℂ) * Complex.I := by
    rw [← Complex.cos_add_sin_I, ← Complex.cos_sub_sin_I, Complex.ofReal_sin]
    ring
  have hid : Complex.exp (((2 * t : ℝ) : ℂ) * Complex.I) - 1 =
      Complex.exp ((t : ℂ) * Complex.I) * (2 * (Real.sin t : ℂ) * Complex.I) := by
    rw [hdouble, Complex.exp_add, ← hdiff, mul_sub, hunit]
  rw [hid]
  simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, RCLike.norm_ofNat, mul_one, one_mul]

/-- Removing an integer leaves the point on the additive unit circle unchanged. -/
theorem coe_sub_int_unitCircle (α : ℝ) (m : ℤ) :
    ((α - (m : ℝ) : ℝ) : AddCircle (1 : ℝ)) = (α : AddCircle (1 : ℝ)) := by
  have hm : ((m : ℝ) : AddCircle (1 : ℝ)) = 0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨m, by simp⟩
  rw [AddCircle.coe_sub, hm, sub_zero]

/-- The chord distance is at least four times the distance to the nearest integer. -/
theorem chord_distance_lower (α : ℝ) :
    4 * integerDistance α ≤ ‖unitCharacter α - 1‖ := by
  let δ : ℝ := α - (round α : ℝ)
  have hδ : |δ| ≤ 1 / 2 := abs_sub_round α
  have hangle : |Real.pi * δ| ≤ Real.pi / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    exact (mul_le_mul_of_nonneg_left hδ Real.pi_pos.le).trans_eq (by ring)
  have hsin := Real.mul_abs_le_abs_sin hangle
  rw [abs_mul, abs_of_pos Real.pi_pos] at hsin
  have hscale : (2 / Real.pi) * (Real.pi * |δ|) = 2 * |δ| := by
    field_simp
  rw [hscale] at hsin
  have hchar : unitCharacter α = Complex.exp (((2 * (Real.pi * δ) : ℝ) : ℂ) * Complex.I) := by
    unfold unitCharacter
    rw [← coe_sub_int_unitCircle α (round α), fourier_coe_apply]
    congr 1
    dsimp [δ]
    push_cast
    ring
  rw [hchar, norm_exp_two_mul_I_sub_one]
  change 4 * |δ| ≤ 2 * |Real.sin (Real.pi * δ)|
  linarith

/-- The sharp elementary reciprocal-distance estimate away from integral phases. -/
theorem norm_linearWeylSum_le_distance (N : ℕ) (α : ℝ) (hα : integerDistance α ≠ 0) :
    ‖linearWeylSum N α‖ ≤ min (N : ℝ) (1 / (2 * integerDistance α)) := by
  have hd : 0 < integerDistance α := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hα)
  have hchord := chord_distance_lower α
  have hz : unitCharacter α ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hchord
    linarith
  refine le_min (norm_linearWeylSum_le_length N α) ?_
  calc
    ‖linearWeylSum N α‖ ≤ 2 / ‖unitCharacter α - 1‖ := norm_linearWeylSum_le_chord N α hz
    _ ≤ 2 / (4 * integerDistance α) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hchord
    _ = 1 / (2 * integerDistance α) := by field_simp; ring

/-- Starting at any integer frequency changes a linear Weyl sum by a unit factor. -/
theorem norm_shiftedLinearWeylSum (M : ℤ) (N : ℕ) (α : ℝ) :
    ‖shiftedLinearWeylSum M N α‖ = ‖linearWeylSum N α‖ := by
  unfold shiftedLinearWeylSum linearWeylSum
  simp_rw [fourier_add]
  rw [← Finset.sum_mul, norm_mul, norm_fourier_value, mul_one]

/-- A total bound: integral phases use the length bound, all other phases use the minimum. -/
def linearSumBound (N : ℕ) (α : ℝ) : ℝ :=
  if integerDistance α = 0 then N else min (N : ℝ) (1 / (2 * integerDistance α))

theorem norm_shiftedLinearWeylSum_le (M : ℤ) (N : ℕ) (α : ℝ) :
    ‖shiftedLinearWeylSum M N α‖ ≤ linearSumBound N α := by
  rw [norm_shiftedLinearWeylSum]
  unfold linearSumBound
  split_ifs with h
  · exact norm_linearWeylSum_le_length N α
  · exact norm_linearWeylSum_le_distance N α h

/-- The same uniform bound in direct complex-exponential notation. -/
theorem norm_exp_linear_sum_le (M : ℤ) (N : ℕ) (α : ℝ) :
    ‖∑ n ∈ Finset.range N,
      Complex.exp (((2 * Real.pi * (α * ((n : ℝ) + M)) : ℝ) : ℂ) * Complex.I)‖ ≤
      linearSumBound N α := by
  have hterm (n : ℕ) :
      Complex.exp (((2 * Real.pi * (α * ((n : ℝ) + M)) : ℝ) : ℂ) * Complex.I) =
        fourier ((n : ℤ) + M) (α : AddCircle (1 : ℝ)) := by
    simpa only [Int.cast_add, Int.cast_natCast] using exp_linear_eq_fourier α ((n : ℤ) + M)
  simp_rw [hterm]
  exact norm_shiftedLinearWeylSum_le M N α

end Waring
