import Waring.ProductBoxSingular
import Waring.ProductBoxScale

/-! # Absolute convergence of the actual mixed singular integral -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Waring.ProductBox
open EndgameCompletion QuadraticModulation

def mixedKernel (k u v L : ℕ) (β : ℝ) : ℂ :=
  monomialIntegral k 1 β^u*productIntegral k L 1 β^v

theorem continuous_mixedKernel (k u v L : ℕ) : Continuous (mixedKernel k u v L) :=
  ((continuous_monomialIntegral k 1).pow u).mul ((continuous_productIntegral k L 1).pow v)

theorem norm_mixedKernel_neg (k u v L : ℕ) (β : ℝ) :
    ‖mixedKernel k u v L (-β)‖=‖mixedKernel k u v L β‖ := by
  simp only [mixedKernel,norm_mul,norm_pow,norm_monomialIntegral_neg k zero_le_one,
    norm_productIntegral_neg k L zero_le_one]

theorem mixedKernel_decay (k u v L : ℕ) (hk : 1≤k) {β : ℝ} (hβ : 0<β) :
    ‖mixedKernel k u v (L+1) β‖≤
      ((2 : ℝ)^u*((2 : ℝ)^(L+1))^v)*β^(-((u : ℝ)+(v : ℝ)/2)/(k : ℝ)) := by
  have hp := productIntegral_decay k L hk hβ.ne'
  have hm := norm_monomialIntegral_decay k hk zero_le_one hβ.ne'
  rw [abs_of_pos hβ] at hp hm
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  calc
    _ = ‖monomialIntegral k 1 β‖^u*‖productIntegral k (L+1) 1 β‖^v := by
      rw [mixedKernel,norm_mul,norm_pow,norm_pow]
    _ ≤ (2*β^(-(k : ℝ)⁻¹))^u*((2 : ℝ)^(L+1)*β^(-(2*(k : ℝ))⁻¹))^v :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hm u)
        (pow_le_pow_left₀ (norm_nonneg _) hp v) (by positivity) (by positivity)
    _ = _ := by
      rw [mul_pow,mul_pow,← Real.rpow_mul_natCast hβ.le,← Real.rpow_mul_natCast hβ.le]
      have he : β^(-(k : ℝ)⁻¹*(u : ℝ))*β^(-(2*(k : ℝ))⁻¹*(v : ℝ))=
          β^(-((u : ℝ)+(v : ℝ)/2)/(k : ℝ)) := by
        rw [← Real.rpow_add hβ]
        congr 1
        field_simp
        ring
      calc
        _ = ((2 : ℝ)^u*((2 : ℝ)^(L+1))^v)*
            (β^(-(k : ℝ)⁻¹*(u : ℝ))*β^(-(2*(k : ℝ))⁻¹*(v : ℝ))) := by ring
        _ = _ := by rw [he]

theorem integrableOn_mixedKernel_tail (k u v L : ℕ) (hk : 1≤k)
    (huv : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) :
    IntegrableOn (mixedKernel k u v (L+1)) (Set.Ioi 1) := by
  have hkpos : (0 : ℝ)<k := by exact_mod_cast (show 0<k by omega)
  have he : -((u : ℝ)+(v : ℝ)/2)/(k : ℝ)< -1 :=
    (div_lt_iff₀ hkpos).mpr (by linarith)
  have hint := (integrableOn_Ioi_rpow_of_lt he zero_lt_one).const_mul
    ((2 : ℝ)^u*((2 : ℝ)^(L+1))^v)
  apply hint.mono' (continuous_mixedKernel k u v (L+1)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with β hβ
  exact mixedKernel_decay k u v L hk (zero_lt_one.trans hβ)

theorem integrable_mixedKernel (k u v L : ℕ) (hk : 1≤k)
    (huv : (k : ℝ)<(u : ℝ)+(v : ℝ)/2) : Integrable (mixedKernel k u v (L+1)) := by
  have hc := continuous_mixedKernel k u v (L+1)
  have hpos : IntegrableOn (mixedKernel k u v (L+1)) (Set.Ioi 0) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
    exact (hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self).union
      (integrableOn_mixedKernel_tail k u v L hk huv)
  have hneg : IntegrableOn (fun β => ‖mixedKernel k u v (L+1) β‖) (Set.Iic 0) := by
    apply (integrableOn_Iic_iff_integrableOn_Iio (f := fun β => ‖mixedKernel k u v (L+1) β‖)).mpr
    have hh := (show IntegrableOn (fun β => ‖mixedKernel k u v (L+1) β‖)
      (Set.Ioi (-(0 : ℝ))) by simpa using hpos.norm).comp_neg_Iio
    simpa only [norm_mixedKernel_neg] using hh
  apply (integrable_norm_iff hc.aestronglyMeasurable).mp
  rw [← integrableOn_univ,← Set.Iic_union_Ioi (a := (0 : ℝ))]
  exact hneg.union hpos.norm

theorem degree8_mixedKernel_integrable (L : ℕ) : Integrable (mixedKernel 8 8 30 (L+1)) :=
  integrable_mixedKernel 8 8 30 L (by omega) (by norm_num)
theorem degree9_mixedKernel_integrable (L : ℕ) : Integrable (mixedKernel 9 11 35 (L+1)) :=
  integrable_mixedKernel 9 11 35 L (by omega) (by norm_num)

#print axioms degree8_mixedKernel_integrable
#print axioms degree9_mixedKernel_integrable
end Waring.ProductBox
