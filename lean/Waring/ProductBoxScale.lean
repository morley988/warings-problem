import Waring.ProductBoxApprox

/-! # Scale and conjugation identities for the literal product integral -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

theorem productIntegral_succ_interval (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    productIntegral k (L+1) M β=∫ t in (0 : ℝ)..M,productIntegral k L M (β*t^k) := by
  unfold productIntegral
  simp only [boxIntegral_succ,productPhase_cons]
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hM]

theorem productIntegral_scale (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    productIntegral k L M β=(M : ℂ)^L*productIntegral k L 1 (β*M^(k*L)) := by
  induction L generalizing β with
  | zero => simp [productIntegral,boxIntegral,productPhase]
  | succ L ih =>
    rw [productIntegral_succ_interval k L hM]
    simp_rw [ih]
    rw [intervalIntegral.integral_const_mul]
    have hscale := intervalIntegral.smul_integral_comp_mul_left
      (fun t : ℝ => productIntegral k L 1 (β*t^k*M^(k*L))) (a := 0) (b := 1) M
    simp only [mul_zero,mul_one,Complex.real_smul] at hscale
    rw [← hscale,productIntegral_succ_interval k L zero_le_one,pow_succ]
    rw [mul_assoc]
    congr 1
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg (productIntegral k L 1)
    dsimp only
    rw [mul_pow]
    calc
      β*(M^k*t^k)*M^(k*L) = β*(M^k*M^(k*L))*t^k := by ring
      _ = _ := by rw [← pow_add]; congr 2 <;> ring

theorem productIntegral_neg (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    productIntegral k L M (-β)=starRingEnd ℂ (productIntegral k L M β) := by
  induction L generalizing β with
  | zero => simp [productIntegral,boxIntegral,productPhase,conj_e]
  | succ L ih =>
    rw [productIntegral_succ_interval k L hM,productIntegral_succ_interval k L hM,
      intervalIntegral.integral_of_le hM,intervalIntegral.integral_of_le hM,← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t _
    change productIntegral k L M (-β*t^k)=starRingEnd ℂ (productIntegral k L M (β*t^k))
    rw [neg_mul,ih]

theorem norm_productIntegral_neg (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    ‖productIntegral k L M (-β)‖=‖productIntegral k L M β‖ := by
  rw [productIntegral_neg k L hM,Complex.norm_conj]

#print axioms productIntegral_scale
#print axioms productIntegral_neg
end Waring.ProductBox
