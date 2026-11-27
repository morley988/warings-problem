import Waring.ShortHeightCounting
import Waring.QuadraticHeight

/-!
# Actual sampled quadratic fourth moments

This composes the proved pointwise quadratic estimate with the proved
short-height counting and dyadic summation. There are no Q1 or Q2 premises.
The explicit bound on the actual finite divisor counts remains a hypothesis;
replacing it by `P^epsilon` requires the usual divisor estimate separately.
-/

noncomputable section

open scoped BigOperators

namespace Waring.SampledQuadratic

open ShortHeightDistribution ShortHeightCounting

/-- A sampled quadratic fourth-moment estimate for actual exponential sums,
arbitrary real modulations, variable integer intervals of length at most P,
and a fixed positive integer leading coefficient. Every logarithm and the
finite divisor-count bound are retained explicitly.
-/
theorem sampled_fourth_moment (s : Finset ℕ) (a b : ℕ → ℤ) (t : ℕ → ℝ)
    (c : ℕ) {H P α D : ℝ} (hc : 0 < c) (hH : 1 ≤ H) (hP : 2 ≤ P)
    (hD0 : 0 ≤ D) (hs : ∀ h ∈ s, 0 < h ∧ (h : ℝ) ≤ H)
    (hab : ∀ h ∈ s, a h ≤ b h)
    (hlength : ∀ h ∈ s, (((b h + 1 - a h).toNat : ℕ) : ℝ) ≤ P)
    (hD : ∀ n ∈ Finset.Icc 1 ⌊2 * H * P⌋₊, (n.divisors.card : ℝ) ≤ D) :
    let A := 1179648 * (c : ℝ) ^ 2 * (2 + Real.log P / Real.log 2) ^ 2
    let K := 256 * D * (2 + 2 * Real.log P / Real.log 2)
    let L := RationalHeight.height (H * P ^ 2) α
    (∑ h ∈ s, ‖∑ z ∈ Finset.Icc (a h) (b h),
      QuadraticModulation.e ((c : ℝ) * ((h : ℝ) * α) * (z : ℝ) ^ 2 + t h * z)‖ ^ 4) ≤
      A * (H * P ^ 2 + P ^ 4 *
        (4 * K * H / P ^ 2 * (2 + Real.log P / Real.log 2) +
          24 * K * min (H / L) (H ^ 2 / L ^ 2))) := by
  have hP1 : 1 ≤ P := (by norm_num : (1 : ℝ) ≤ 2).trans hP
  have hPpos : 0 < P := zero_lt_one.trans_le hP1
  obtain ⟨T, hcover, hcover2⟩ := exists_dyadic_cover zero_lt_one hP1
  simp only [one_mul] at hcover hcover2
  have hdepth := dyadic_depth_le_log (a := 1) T le_rfl hPpos
    (by simpa only [one_mul] using hcover2)
  have hdepthsq := pow_le_pow_left₀ (show (0 : ℝ) ≤ (T + 1 : ℕ) by positivity) hdepth 2
  let Z : ℕ → ℂ := fun h => ∑ z ∈ Finset.Icc (a h) (b h),
    QuadraticModulation.e ((c : ℝ) * ((h : ℝ) * α) * (z : ℝ) ^ 2 + t h * z)
  let B : ℕ → ℝ := fun h => RationalHeight.height (P ^ 2) ((h : ℝ) * α)
  have hpoint : ∀ h ∈ s, ‖Z h‖ ^ 4 ≤
      (1179648 * (c : ℝ) ^ 2 * (2 + Real.log P / Real.log 2) ^ 2) *
        (P ^ 2 + P ^ 4 / (B h) ^ 2) := by
    intro h hh
    have hb := QuadraticHeight.quadratic_interval_fourth_height_integer_coefficient
      (a h) (b h) ((h : ℝ) * α) (t h) P c T hc (hab h hh) hP1 (hlength h hh) hcover
    apply hb.trans
    apply mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdepthsq (by positivity))
    positivity
  exact fourth_moment_sum_bound s Z B (by positivity)
    (card_le_real_bound s (zero_le_one.trans hH) hs)
    (short_height_inverse_square_log_bound s (α := α) hH hP hD0 hs hD) hpoint

#print axioms sampled_fourth_moment

end Waring.SampledQuadratic
