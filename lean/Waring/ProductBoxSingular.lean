import Waring.ProductBoxApprox
import Waring.EndgameCompletionSingular

/-! # Decay of the actual product-box singular integral

Each additional product coordinate costs an integrable t^(-1/2) weight.
The resulting saving is uniform in frequency, with an explicit L-dependent
constant. No distribution theorem for smooth integers is assumed.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

theorem productIntegral_succ (k L : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    productIntegral k (L+1) M β=∫ t in (0 : ℝ)..M,productIntegral k L M (β*t^k) := by
  unfold productIntegral
  simp only [boxIntegral_succ,productPhase_cons]
  rw [integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hM]

theorem productIntegral_one (k : ℕ) {M : ℝ} (hM : 0≤M) (β : ℝ) :
    productIntegral k 1 M β=monomialIntegral k M β := by
  rw [productIntegral_succ k 0 hM]
  simp only [productIntegral,boxIntegral,productPhase,Finset.univ_eq_empty,Finset.prod_empty,
    one_pow,mul_one,monomialIntegral]

theorem norm_monomialIntegral_half_decay (k : ℕ) (hk : 1≤k) {β : ℝ} (hβ : β≠0) :
    ‖monomialIntegral k 1 β‖≤2*|β|^(-(2*(k : ℝ))⁻¹) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have he : -(k : ℝ)⁻¹≤-(2*(k : ℝ))⁻¹ := by
    apply neg_le_neg
    exact inv_anti₀ hkpos (by linarith)
  by_cases hb : 1≤|β|
  · exact (norm_monomialIntegral_decay k hk zero_le_one hβ).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hb he) (by norm_num))
  · have hpow := Real.one_le_rpow_of_pos_of_le_one_of_nonpos (abs_pos.mpr hβ)
      (le_of_not_ge hb) (show -(2*(k : ℝ))⁻¹≤0 by exact neg_nonpos.mpr (inv_nonneg.mpr (by positivity)))
    exact (norm_monomialIntegral_le k zero_le_one β).trans (by nlinarith)

theorem integral_half_power : (∫ t in (0 : ℝ)..1,t^(-(1/2 : ℝ)))=2 := by
  rw [integral_rpow (Or.inl (by norm_num : -1 < -(1/2 : ℝ)))]
  norm_num

theorem productIntegral_decay (k L : ℕ) (hk : 1≤k) {β : ℝ} (hβ : β≠0) :
    ‖productIntegral k (L+1) 1 β‖≤(2 : ℝ)^(L+1)*|β|^(-(2*(k : ℝ))⁻¹) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  induction L generalizing β with
  | zero => simpa only [Nat.zero_add,pow_one,productIntegral_one k zero_le_one] using
      norm_monomialIntegral_half_decay k hk hβ
  | succ L ih =>
    rw [productIntegral_succ k (L+1) zero_le_one]
    have hc : Continuous (fun t : ℝ => productIntegral k (L+1) 1 (β*t^k)) :=
      (continuous_productIntegral k (L+1) 1).comp (continuous_const.mul (continuous_id.pow k))
    have hir : IntervalIntegrable (fun t : ℝ => t^(-(1/2 : ℝ))) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by norm_num)
    have hrint : IntegrableOn (fun t : ℝ => t^(-(1/2 : ℝ))) (Set.Ioc 0 1) := hir.1
    have hpoint {t : ℝ} (ht : t ∈ Set.Ioc 0 1) :
        ‖productIntegral k (L+1) 1 (β*t^k)‖≤
          ((2 : ℝ)^(L+1)*|β|^(-(2*(k : ℝ))⁻¹))*t^(-(1/2 : ℝ)) := by
      have hh := ih (mul_ne_zero hβ (pow_ne_zero k ht.1.ne'))
      convert hh using 1
      rw [abs_mul,abs_of_nonneg (pow_nonneg ht.1.le _),Real.mul_rpow (abs_nonneg _) (pow_nonneg ht.1.le k),
        ← Real.rpow_natCast t k,← Real.rpow_mul ht.1.le]
      have he : (k : ℝ)*(-(2*(k : ℝ))⁻¹)=-(1/2 : ℝ) := by field_simp
      rw [he]
      ring
    calc
      _ ≤ ∫ t in Set.Ioc 0 1,‖productIntegral k (L+1) 1 (β*t^k)‖ := by
        simpa only [intervalIntegral.integral_of_le zero_le_one] using
          intervalIntegral.norm_integral_le_integral_norm zero_le_one
      _ ≤ ∫ t in Set.Ioc 0 1,((2 : ℝ)^(L+1)*|β|^(-(2*(k : ℝ))⁻¹))*t^(-(1/2 : ℝ)) := by
        apply integral_mono_ae
          (hc.norm.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
          (hrint.const_mul _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        exact hpoint ht
      _ = _ := by
        rw [integral_const_mul,← intervalIntegral.integral_of_le zero_le_one,integral_half_power]
        rw [pow_succ]
        ring

#print axioms productIntegral_decay
end Waring.ProductBox
