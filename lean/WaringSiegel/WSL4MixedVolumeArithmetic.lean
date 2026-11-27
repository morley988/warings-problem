import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exact real-power bookkeeping for the mixed sixth-moment boxes -/
namespace WaringSiegel.WSL4Local

theorem mixed_diagonal_volume_bound (X Y ε : ℝ) (hX : 0<X) (hY : 1≤Y)
    (hYX : Y^7≤X) (hε : 0≤ε) :
    Y*X*(X/Y)^(2+ε) ≤ X^((7:ℝ)/2+ε)*Y^(-(9/2):ℝ) := by
  have hY0 : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hratio : 0<X/Y := div_pos hX hY0
  have hratioX : X/Y≤X := div_le_self hX.le hY
  have hpowε := Real.rpow_le_rpow hratio.le hratioX hε
  have hhalf := Real.rpow_le_rpow (pow_nonneg hY0.le 7) hYX (by norm_num : (0:ℝ)≤1/2)
  have hYhalf : (Y^7:ℝ)^(1/2:ℝ)=Y^(7/2:ℝ) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hY0.le]
    norm_num
  rw [hYhalf] at hhalf
  have hYfactor : Y^(-1:ℝ) ≤ X^(1/2:ℝ)*Y^(-(9/2):ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hhalf
      (Real.rpow_nonneg hY0.le (-(9/2):ℝ))
    rw [← Real.rpow_add hY0] at hh
    norm_num at hh ⊢
    exact hh
  have hleft : Y*X*(X/Y)^(2+ε)=X^3*Y^(-1:ℝ)*(X/Y)^ε := by
    rw [Real.rpow_add hratio,Real.rpow_two,Real.rpow_neg_one]
    field_simp
    <;> ring
  have hXp : X^3*X^ε*X^(1/2:ℝ)=X^((7:ℝ)/2+ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_add hX,← Real.rpow_add hX]
    congr 1
    ring
  rw [hleft]
  calc
    _ ≤ X^3*Y^(-1:ℝ)*X^ε :=
      mul_le_mul_of_nonneg_left hpowε (by positivity)
    _ = (X^3*X^ε)*Y^(-1:ℝ) := by ring
    _ ≤ (X^3*X^ε)*(X^(1/2:ℝ)*Y^(-(9/2):ℝ)) :=
      mul_le_mul_of_nonneg_left hYfactor (by positivity)
    _ = _ := by rw [← mul_assoc,hXp]

theorem mixed_kernel_epsilon_absorb (X Y C D ε : ℝ) (hX : 0<X)
    (hY : 0≤Y) (hYX : Y≤X) (hC : 0≤C) (hD : 0≤D) (hε : 0≤ε) :
    C*(D*Y^3)^(ε/4)*(X^((7:ℝ)/2+ε/4)*Y^(-(9/2):ℝ)) ≤
      (C*D^(ε/4))*X^((7:ℝ)/2+ε)*Y^(-(9/2):ℝ) := by
  rw [Real.mul_rpow hD (pow_nonneg hY 3),← Real.rpow_natCast_mul hY]
  have hp := Real.rpow_le_rpow hY hYX (by linarith : 0≤(3:ℝ)*(ε/4))
  calc
    _ = (C*D^(ε/4))*Y^((3:ℝ)*(ε/4))*X^((7:ℝ)/2+ε/4)*Y^(-(9/2):ℝ) := by ring
    _ ≤ (C*D^(ε/4))*X^((3:ℝ)*(ε/4))*X^((7:ℝ)/2+ε/4)*Y^(-(9/2):ℝ) := by
      gcongr
    _ = _ := by
      rw [mul_assoc (C*D^(ε/4)),← Real.rpow_add hX]
      congr 2
      ring

#print axioms mixed_diagonal_volume_bound
#print axioms mixed_kernel_epsilon_absorb
end WaringSiegel.WSL4Local
