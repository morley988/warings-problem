import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arithmetic sublemmas for the adapted coefficient sampling estimate

These prove the exact exceptional-approximant rigidity and denominator
cancellation, and the algebra combining two reciprocal bounds. They do not
assert the large-sieve estimate, divisor-count bound, or complete sampling
inequality: those analytic steps remain to be formalized.
-/

namespace Waring.SamplingArithmetic

/-- An integer strictly within distance one of zero is exactly zero. -/
theorem int_eq_zero_of_abs_cast_lt_one {z : ℤ} (h : |(z : ℝ)| < 1) : z = 0 := by
  have hi : |z| < (1 : ℤ) := by exact_mod_cast h
  have hh := abs_lt.mp hi
  omega

/-- The cross product of two integer approximants is controlled by their two
approximation errors. No positivity or coprimality is needed for this identity.
-/
theorem cross_error_bound (a c h s t : ℤ) (α : ℝ) :
    |((a * h ^ 3 * s - c * t : ℤ) : ℝ)| ≤
      |(h : ℝ) ^ 3 * (s : ℝ)| * |(t : ℝ) * α - a| +
      |(t : ℝ)| * |α * (h : ℝ) ^ 3 * (s : ℝ) - c| := by
  have hid : ((a * h ^ 3 * s - c * t : ℤ) : ℝ) =
      -((h : ℝ) ^ 3 * (s : ℝ)) * ((t : ℝ) * α - a) +
        (t : ℝ) * (α * (h : ℝ) ^ 3 * (s : ℝ) - c) := by
    push_cast
    ring
  rw [hid]
  calc
    |-((h : ℝ) ^ 3 * (s : ℝ)) * ((t : ℝ) * α - a) +
        (t : ℝ) * (α * (h : ℝ) ^ 3 * (s : ℝ) - c)| ≤
      |-((h : ℝ) ^ 3 * (s : ℝ)) * ((t : ℝ) * α - a)| +
        |(t : ℝ) * (α * (h : ℝ) ^ 3 * (s : ℝ) - c)| := abs_add_le _ _
    _ = _ := by simp only [abs_mul, abs_neg]

/-- The strict exceptional-arc bound forces equality of the cross products. -/
theorem exceptional_rigidity {a c h s t : ℤ} {α : ℝ}
    (hsmall : |(h : ℝ) ^ 3 * (s : ℝ)| * |(t : ℝ) * α - a| +
      |(t : ℝ)| * |α * (h : ℝ) ^ 3 * (s : ℝ) - c| < 1) :
    a * h ^ 3 * s = c * t := by
  exact sub_eq_zero.mp (int_eq_zero_of_abs_cast_lt_one
    ((cross_error_bound a c h s t α).trans_lt hsmall))

/-- Reduction of `c/s` makes its denominator divide the common denominator. -/
theorem exceptional_denominator_divides {a c h s t : ℤ}
    (hcs : IsCoprime c s) (heq : a * h ^ 3 * s = c * t) : s ∣ t := by
  apply hcs.symm.dvd_of_dvd_mul_left
  rw [← heq]
  exact dvd_mul_left s (a * h ^ 3)

/-- Both reduced fractions force the divisor class `t/s` to divide `h^3`.
This statement uses integer division, with exact divisibility already proved.
-/
theorem exceptional_quotient_divides_cube {a c h s t : ℤ}
    (hat : IsCoprime a t) (hcs : IsCoprime c s) (hs : s ≠ 0)
    (heq : a * h ^ 3 * s = c * t) : s ∣ t ∧ t / s ∣ h ^ 3 := by
  have hst := exceptional_denominator_divides hcs heq
  refine ⟨hst, ?_⟩
  have htprod : t ∣ h ^ 3 * s := by
    apply hat.symm.dvd_of_dvd_mul_left
    rw [← mul_assoc, heq]
    exact dvd_mul_left t c
  rcases hst with ⟨d, hd⟩
  have hdcube : d ∣ h ^ 3 := by
    apply (mul_dvd_mul_iff_left hs).mp
    simpa only [hd, mul_comm (h ^ 3) s] using htprod
  rw [hd, Int.mul_ediv_cancel_left d hs]
  exact hdcube

/-- A direct composition of the closeness and coprimality conditions. -/
theorem exceptional_divisor_class {a c h s t : ℤ} {α : ℝ}
    (hat : IsCoprime a t) (hcs : IsCoprime c s) (hs : s ≠ 0)
    (hsmall : |(h : ℝ) ^ 3 * (s : ℝ)| * |(t : ℝ) * α - a| +
      |(t : ℝ)| * |α * (h : ℝ) ^ 3 * (s : ℝ) - c| < 1) :
    s ∣ t ∧ t / s ∣ h ^ 3 :=
  exceptional_quotient_divides_cube hat hcs hs (exceptional_rigidity hsmall)

/-- Combining a trivial and a reciprocal estimate, including the zero-error
case. At `v=0` the second estimate is not required, avoiding division by zero.
-/
theorem combine_reciprocal_bounds {X A u v : ℝ}
    (hA : 0 ≤ A) (hu : 0 < u) (hv : 0 ≤ v)
    (hfirst : X ≤ A / u) (hsecond : 0 < v → X ≤ A / v) :
    X ≤ 2 * A / (u + v) := by
  have hsum : 0 < u + v := add_pos_of_pos_of_nonneg hu hv
  by_cases hcase : v ≤ u
  · apply hfirst.trans
    apply (div_le_div_iff₀ hu hsum).mpr
    have hprod := mul_nonneg hA (sub_nonneg.mpr hcase)
    nlinarith
  · have huv : u < v := lt_of_not_ge hcase
    have hvpos : 0 < v := hu.trans huv
    apply (hsecond hvpos).trans
    apply (div_le_div_iff₀ hvpos hsum).mpr
    have hprod := mul_nonneg hA (sub_nonneg.mpr huv.le)
    nlinarith

/-- The scalar height denominator obtained from a divisor class. Here
`B = J*N*abs(beta)` in the application. A factor two is harmless in the
analytic estimate, and the conclusion remains valid at beta equal to zero.
-/
theorem divisor_class_height_bound {X H t B : ℝ}
    (hH : 0 ≤ H) (ht : 0 < t) (hB : 0 ≤ B)
    (htrivial : X ≤ H ^ 3 / t)
    (hdecay : 0 < H ^ 3 * t * B → X ≤ H ^ 3 / (H ^ 3 * t * B)) :
    X ≤ 2 * H ^ 3 / (t + H ^ 3 * t * B) :=
  combine_reciprocal_bounds (pow_nonneg hH _) ht
    (mul_nonneg (mul_nonneg (pow_nonneg hH _) ht.le) hB) htrivial hdecay

#print axioms exceptional_divisor_class
#print axioms combine_reciprocal_bounds
#print axioms divisor_class_height_bound

end Waring.SamplingArithmetic
