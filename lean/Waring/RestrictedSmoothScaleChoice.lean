import Waring.RestrictedSmoothScale

/-! # The exact rational-arc scale and uniform smoothness loss -/

noncomputable section
namespace Waring.RestrictedSmoothArcs

def arcRootScale (k : ℕ) (Q : ℝ) : ℝ := (2*Q)^(2/(k : ℝ))

theorem arcRootScale_one_le (k : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) :
    1 ≤ arcRootScale k Q :=
  Real.one_le_rpow (by linarith) (div_nonneg (by norm_num) (Nat.cast_nonneg _))

theorem arcRootScale_pow {k : ℕ} (hk : 1 ≤ k) {Q : ℝ} (hQ : 1 ≤ Q) :
    (arcRootScale k Q)^k=4*Q^2 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hk)
  unfold arcRootScale
  rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ 2*Q),
    div_mul_cancel₀ _ hk0,Real.rpow_two]
  ring

theorem arcRootScale_rpow (k : ℕ) {Q : ℝ} (hQ : 1 ≤ Q) (D : ℝ) :
    (arcRootScale k Q)^D=(2 : ℝ)^(2*D/(k : ℝ))*Q^(2*D/(k : ℝ)) := by
  unfold arcRootScale
  rw [← Real.rpow_mul (by linarith : 0 ≤ 2*Q),
    show (2/(k : ℝ))*D=2*D/(k : ℝ) by ring,
    Real.mul_rpow (by norm_num) (zero_le_one.trans hQ)]

theorem large_scale_power {P T R D : ℝ} (hP : 0 ≤ P) (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hD : 0 ≤ D) (hlarge : ¬T*R^2 ≤ P) :
    P^D ≤ T^D*R^(2*D) := by
  calc
    _ ≤ (T*R^2)^D := Real.rpow_le_rpow hP (le_of_lt (lt_of_not_ge hlarge)) hD
    _ = _ := by rw [Real.mul_rpow hT (sq_nonneg R),← Real.rpow_natCast_mul hR]; norm_num

theorem smoothness_loss_absorption {P R L ε η : ℝ}
    (hP : 1 ≤ P) (hR : 0 ≤ R) (hRP : R ≤ P^η) (hL : 0 < L)
    (hη : η ≤ ε/(2*L)) : R^L ≤ P^(ε/2) := by
  have hbudget : η*L ≤ ε/2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2*L)).mp hη
    nlinarith
  calc
    _ ≤ (P^η)^L := Real.rpow_le_rpow hR hRP hL.le
    _ = P^(η*L) := (Real.rpow_mul (zero_le_one.trans hP) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hP hbudget

#print axioms arcRootScale_pow
#print axioms smoothness_loss_absorption
end Waring.RestrictedSmoothArcs
