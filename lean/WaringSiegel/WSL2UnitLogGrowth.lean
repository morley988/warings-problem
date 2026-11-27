import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing the logarithmic unit factor into an arbitrary small power

This is a closed elementary inequality, used after the actual logarithmic
unit count. It adds no growth assumption to the divisor estimate.
-/

namespace WaringSiegel.WSL2

/-- For every positive epsilon, any fixed power of 1+log L is bounded by
C L^epsilon uniformly for all L at least one. -/
theorem exists_one_add_log_pow_le_rpow (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (1 + Real.log L) ^ n ≤ C * L ^ ε := by
  let a : ℝ := ε / (n + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨(1 + a⁻¹) ^ n, pow_pos (by positivity) _, ?_⟩
  intro L hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hp : 1 ≤ L ^ a := Real.one_le_rpow hL ha.le
  have hl := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hLp a)
  rw [Real.log_rpow hLp] at hl
  have hla : Real.log L ≤ a⁻¹ * L ^ a := by
    have hm := mul_le_mul_of_nonneg_left hl (inv_pos.mpr ha).le
    rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul] at hm
    nlinarith [inv_pos.mpr ha]
  have hbase : 1 + Real.log L ≤ (1 + a⁻¹) * L ^ a := by nlinarith
  have hexp : a * (n : ℝ) ≤ ε := by
    have hn : (0 : ℝ) < n + 1 := by positivity
    have he : a * ((n : ℝ) + 1) = ε := by dsimp [a]; field_simp
    nlinarith
  calc
    (1 + Real.log L) ^ n ≤ ((1 + a⁻¹) * L ^ a) ^ n :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = (1 + a⁻¹) ^ n * L ^ (a * (n : ℝ)) := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
    _ ≤ (1 + a⁻¹) ^ n * L ^ ε :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL hexp) (by positivity)

end WaringSiegel.WSL2

#print axioms WaringSiegel.WSL2.exists_one_add_log_pow_le_rpow
