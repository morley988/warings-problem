import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The ordinary-differencing diagonal cap

A diagonal loss P^-1 and a resource saving P^-S combine as P^-min(1,S).
Taking the positive root gives exactly the 2^(j-k+2) exponent used by
the certificate; neither a diagonal nor a root factor is discarded.
-/

noncomputable section
namespace Waring.DiagonalCap

theorem two_power_terms {P S : ℝ} (hP : 1 ≤ P) :
    P^(-1:ℝ)+P^(-S) ≤ 2*P^(-min 1 S) := by
  have h1 := Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg (min_le_left 1 S))
  have h2 := Real.rpow_le_rpow_of_exponent_le hP (neg_le_neg (min_le_right 1 S))
  linarith

theorem root_of_diagonal_bound {F A C P S : ℝ} {q : ℕ}
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hP : 1 ≤ P) (hq : q ≠ 0)
    (hbound : F^q ≤ C*A^q*(P^(-1:ℝ)+P^(-S))) :
    F ≤ (2*C)^((q:ℝ)⁻¹)*A*P^(-min 1 S/(q:ℝ)) := by
  have hP0 : 0 ≤ P := zero_le_one.trans hP
  have hPp : 0 < P := zero_lt_one.trans_le hP
  have hsum := two_power_terms (S:=S) hP
  have hh : F^q ≤ (2*C)*A^q*P^(-min 1 S) := by
    calc
      F^q ≤ C*A^q*(P^(-1:ℝ)+P^(-S)) := hbound
      _ ≤ C*A^q*(2*P^(-min 1 S)) := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by ring
  have hr := Real.rpow_le_rpow (pow_nonneg hF q) hh
    (show 0 ≤ (q:ℝ)⁻¹ by positivity)
  rw [Real.pow_rpow_inv_natCast hF hq] at hr
  calc
    F ≤ ((2*C)*A^q*P^(-min 1 S))^((q:ℝ)⁻¹) := hr
    _ = ((2*C)^((q:ℝ)⁻¹)*(A^q)^((q:ℝ)⁻¹))*(P^(-min 1 S))^((q:ℝ)⁻¹) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hP0 _),
        Real.mul_rpow (by positivity) (pow_nonneg hA q)]
    _ = (2*C)^((q:ℝ)⁻¹)*A*P^(-min 1 S/(q:ℝ)) := by
      rw [Real.pow_rpow_inv_natCast hA hq, ← Real.rpow_mul hP0]
      simp only [div_eq_mul_inv]

/-- In the selected policies q=2^r with r=0,1,2. The theorem is valid
for every finite number of ordinary differencing stages. -/
theorem ordinary_differencing_cap {F A C P S : ℝ} (r : ℕ)
    (hF : 0 ≤ F) (hA : 0 ≤ A) (hC : 0 ≤ C) (hP : 1 ≤ P)
    (hbound : F^(2^r) ≤ C*A^(2^r)*(P^(-1:ℝ)+P^(-S))) :
    F ≤ (2*C)^(((2:ℝ)^r)⁻¹)*A*P^(-min 1 S/((2:ℝ)^r)) := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using
    root_of_diagonal_bound hF hA hC hP (pow_ne_zero r (by norm_num : (2:ℕ)≠0)) hbound

#print axioms ordinary_differencing_cap

end Waring.DiagonalCap
