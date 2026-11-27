import Waring.GeometricSums
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Separation of short blocks under a good rational approximant

Reducedness of the rational approximant and its denominator-error product
bound imply reciprocal spacing on blocks of length at most half the
denominator. The separation estimate is proved against every integer before
specializing to nearest integers, so the treatment includes rounding ties.
-/

noncomputable section

namespace Waring.RationalSpacing

/-- The signed representative nearest zero, with the library's fixed choice
at half-integers. Its absolute value is `integerDistance`. -/
def signedFraction (x : ℝ) : ℝ := x - (round x : ℝ)

@[simp] theorem abs_signedFraction (x : ℝ) :
    |signedFraction x| = Waring.integerDistance x := rfl

theorem abs_signedFraction_le (x : ℝ) : |signedFraction x| ≤ 1 / 2 := abs_sub_round x

/-- A short nonzero integer cannot be a multiple of the reduced denominator. -/
theorem short_cross_product_ne_zero (r : ℚ) {d : ℤ} (hd : d ≠ 0)
    (hshort : |(d : ℝ)| ≤ (r.den : ℝ) / 2) (m : ℤ) :
    r.num * d - (r.den : ℤ) * m ≠ 0 := by
  intro hzero
  have hcross : r.num * d = (r.den : ℤ) * m := sub_eq_zero.mp hzero
  have hdiv : (r.den : ℤ) ∣ r.num * d := ⟨m, hcross⟩
  have hdivN : r.den ∣ r.num.natAbs * d.natAbs := by
    simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp hdiv
  have hdd : r.den ∣ d.natAbs := r.reduced.symm.dvd_of_dvd_mul_left hdivN
  have hdnpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  have hleN : r.den ≤ d.natAbs := Nat.le_of_dvd hdnpos hdd
  have hleZ : (r.den : ℤ) ≤ |d| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hleN
  have hleR : (r.den : ℝ) ≤ |(d : ℝ)| := by exact_mod_cast hleZ
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  linarith

/-- Separation from every integer, obtained directly from the nonzero
integer cross product. The denominator-error hypothesis is `|alpha-a/q|≤q⁻²`.
-/
theorem distance_to_integer_lower (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    {d : ℤ} (hd : d ≠ 0) (hshort : |(d : ℝ)| ≤ (r.den : ℝ) / 2) (m : ℤ) :
    1 / (2 * (r.den : ℝ)) ≤ |α * (d : ℝ) - (m : ℝ)| := by
  have hq : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hcross := short_cross_product_ne_zero r hd hshort m
  have h1Z : (1 : ℤ) ≤ |r.num * d - (r.den : ℤ) * m| := by
    have h := abs_pos.mpr hcross
    omega
  have h1 : (1 : ℝ) ≤ |((r.num * d - (r.den : ℤ) * m : ℤ) : ℝ)| := by
    exact_mod_cast h1Z
  have hid : ((r.num * d - (r.den : ℤ) * m : ℤ) : ℝ) =
      (r.den : ℝ) * (α * (d : ℝ) - (m : ℝ)) -
        (d : ℝ) * ((r.den : ℝ) * α - (r.num : ℝ)) := by
    push_cast
    ring
  have htriangle : 1 ≤ (r.den : ℝ) * |α * (d : ℝ) - (m : ℝ)| +
      |(d : ℝ)| * |(r.den : ℝ) * α - (r.num : ℝ)| := by
    apply h1.trans
    rw [hid]
    apply (abs_sub _ _).trans
    rw [abs_mul, abs_mul, abs_of_pos hq]
  have herror : |(d : ℝ)| * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_right hshort
      (abs_nonneg ((r.den : ℝ) * α - (r.num : ℝ)))
    nlinarith
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hq)).mpr
  nlinarith

/-- The usual distance to the nearest integer has the same lower bound. -/
theorem integerDistance_lower (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    {d : ℤ} (hd : d ≠ 0) (hshort : |(d : ℝ)| ≤ (r.den : ℝ) / 2) :
    1 / (2 * (r.den : ℝ)) ≤ Waring.integerDistance (α * (d : ℝ)) :=
  distance_to_integer_lower r hgood hd hshort (round (α * (d : ℝ)))

/-- Signed fractional representatives of two nearby distinct multiples are
separated in the real line. There is no assumption about their signs. -/
theorem signedFraction_separation (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    {u v : ℤ} (hne : u ≠ v) (hshort : |((u - v : ℤ) : ℝ)| ≤ (r.den : ℝ) / 2) :
    1 / (2 * (r.den : ℝ)) ≤
      |signedFraction (α * (u : ℝ)) - signedFraction (α * (v : ℝ))| := by
  have h := distance_to_integer_lower r hgood (sub_ne_zero.mpr hne) hshort
    (round (α * (u : ℝ)) - round (α * (v : ℝ)))
  convert h using 1
  congr 1
  unfold signedFraction
  push_cast
  ring

/-- A convenient interval version for applying finite separated-point
counting and reciprocal-sum estimates block by block. -/
theorem signedFraction_separation_on_interval (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    {a b u v : ℤ} (hwidth : ((b - a : ℤ) : ℝ) ≤ (r.den : ℝ) / 2)
    (hu : a ≤ u ∧ u ≤ b) (hv : a ≤ v ∧ v ≤ b) (hne : u ≠ v) :
    1 / (2 * (r.den : ℝ)) ≤
      |signedFraction (α * (u : ℝ)) - signedFraction (α * (v : ℝ))| := by
  apply signedFraction_separation r hgood hne
  have hdZ : |u - v| ≤ b - a := abs_le.mpr ⟨by omega, by omega⟩
  have hdR : |((u - v : ℤ) : ℝ)| ≤ ((b - a : ℤ) : ℝ) := by exact_mod_cast hdZ
  exact hdR.trans hwidth

/-- A block of `q/2+1` consecutive indices has the required separation,
including when the reduced denominator is one. -/
theorem signedFraction_separation_block (r : ℚ) {α : ℝ}
    (hgood : (r.den : ℝ) * |(r.den : ℝ) * α - (r.num : ℝ)| ≤ 1)
    (M : ℤ) {u v : ℕ} (hu : u < r.den / 2 + 1) (hv : v < r.den / 2 + 1)
    (hne : u ≠ v) :
    1 / (2 * (r.den : ℝ)) ≤
      |signedFraction (α * ((M + (u : ℤ) : ℤ) : ℝ)) -
        signedFraction (α * ((M + (v : ℤ) : ℤ) : ℝ))| := by
  have hhalf : ((r.den / 2 : ℕ) : ℝ) * 2 ≤ (r.den : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self r.den 2
  have hwidth : (((M + (r.den / 2 : ℕ) - M : ℤ) : ℝ)) ≤ (r.den : ℝ) / 2 := by
    have hhalf' : ((r.den / 2 : ℕ) : ℝ) ≤ (r.den : ℝ) / 2 := by linarith
    simpa only [add_sub_cancel_left, Int.cast_natCast] using hhalf'
  apply signedFraction_separation_on_interval r hgood hwidth
  · constructor
    · exact le_add_of_nonneg_right (Int.natCast_nonneg u)
    · exact add_le_add_left (by exact_mod_cast Nat.le_of_lt_succ hu) M
  · constructor
    · exact le_add_of_nonneg_right (Int.natCast_nonneg v)
    · exact add_le_add_left (by exact_mod_cast Nat.le_of_lt_succ hv) M
  · intro heq
    apply hne
    exact_mod_cast add_left_cancel heq

#print axioms distance_to_integer_lower
#print axioms signedFraction_separation_on_interval
#print axioms signedFraction_separation_block

end Waring.RationalSpacing
