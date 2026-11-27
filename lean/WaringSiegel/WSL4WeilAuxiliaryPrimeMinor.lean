import WaringSiegel.WSL4WeilAuxiliaryPrimeVolume

/-! # The actual cubic outer-minor size is negligible relative to the main scale -/
noncomputable section
set_option maxHeartbeats 1000000
namespace WaringSiegel.WSL4Weil
open Filter Topology
open scoped Classical

theorem auxiliary_minor_relative_power_bound (C ε X Y : ℝ)
    (hC : 0 ≤ C) (hX : 0 < X) (hY : 0 < Y) (hXY : X^(1/10 : ℝ) ≤ Y) :
    C*X^(5+ε)*Y^(-9/2 : ℝ) ≤ (C*X^(ε-1/20))*(X^5/Y^4) := by
  have hy : Y^(-1/2 : ℝ) ≤ X^(-1/20 : ℝ) := by
    calc
      _ ≤ (X^(1/10 : ℝ))^(-1/2 : ℝ) :=
        Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hX _) hXY (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hX.le]; congr 1; norm_num
  have hxprod : X^(5+ε) = X^5*X^ε := by
    rw [Real.rpow_add hX]
    rw [show X^(5 : ℝ)=X^(5 : ℕ) from Real.rpow_natCast X 5]
  have hyprod : Y^(-9/2 : ℝ) = Y^(-1/2 : ℝ)/Y^4 := by
    rw [show (-9/2 : ℝ)=(-1/2 : ℝ)-(4 : ℕ) by norm_num,Real.rpow_sub hY,Real.rpow_natCast]
  have hfactor : C*X^(5+ε)*Y^(-9/2 : ℝ) =
      (C*X^ε*Y^(-1/2 : ℝ))*(X^5/Y^4) := by
    rw [hxprod,hyprod]
    ring
  have hcoef : C*X^ε*X^(-1/20 : ℝ)=C*X^(ε-1/20) := by
    rw [mul_assoc,← Real.rpow_add hX]
    congr 1
    ring
  rw [hfactor]
  calc
    _ ≤ (C*X^ε*X^(-1/20 : ℝ))*(X^5/Y^4) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hy (mul_nonneg hC (Real.rpow_nonneg hX.le _)))
        (div_nonneg (pow_nonneg hX.le _) (pow_nonneg hY.le _))
    _ = _ := by rw [hcoef]

theorem exists_auxiliary_minor_relative_small (C c ε : ℝ)
    (hC : 0 ≤ C) (hc : 0 < c) (hε : ε < 1/20) :
    ∃ X0 : ℝ, 1 ≤ X0 ∧ ∀ X : ℝ, X0 < X → ∀ Y : ℝ,
      X^(1/10 : ℝ) ≤ Y → C*X^(5+ε)*Y^(-9/2 : ℝ) < c*X^5/Y^4 := by
  have hlim : Tendsto (fun X : ℝ => C*X^(ε-1/20)) atTop (𝓝 0) := by
    simpa only [neg_sub,mul_zero] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hε)).const_mul C
  obtain ⟨M,hM⟩ := eventually_atTop.mp (hlim.eventually_lt_const hc)
  refine ⟨max 1 M,le_max_left _ _,fun X hX Y hXY => ?_⟩
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hX.le)
  have hY0 : 0 < Y := (Real.rpow_pos_of_pos hX0 _).trans_le hXY
  have hratio := hM X ((le_max_right _ _).trans hX.le)
  apply (auxiliary_minor_relative_power_bound C ε X Y hC hX0 hY0 hXY).trans_lt
  exact (mul_lt_mul_of_pos_right hratio
    (div_pos (pow_pos hX0 5) (pow_pos hY0 4))).trans_eq (by ring)
end WaringSiegel.WSL4Weil

#print axioms WaringSiegel.WSL4Weil.auxiliary_minor_relative_power_bound
#print axioms WaringSiegel.WSL4Weil.exists_auxiliary_minor_relative_small
