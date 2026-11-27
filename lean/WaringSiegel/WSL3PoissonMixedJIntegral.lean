import WaringSiegel.WSL3PoissonMixedJExpansion
import WaringSiegel.WSL3PoissonMixedKWhole

/-! # The actual J integral reduced to K of actual sixth-power differences -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Function Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding WaringSiegel.WSL2
open scoped NumberField Classical BigOperators ContDiff nonZeroDivisors ComplexConjugate
namespace WaringSiegel.WSL3Poisson
variable {K : Type*} [Field K] [NumberField K]

theorem compactMixedJIntegral_expansion (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) :
    compactMixedJIntegral u w v huc hwc hvc H M R hH hM hR =
      ∑ p : compactIntegerSupport w hwc M hM × compactIntegerSupport w hwc M hM,
        (w (M⁻¹ • mixedEmbedding K ((p.1:𝓞 K):K))*
          conj (w (M⁻¹ • mixedEmbedding K ((p.2:𝓞 K):K)))) *
          ∫ q, compactTraceNonzeroCubicSum u huc H hH
            (traceTorusMul ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) q) *
            ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ) ∂traceHaar := by
  let E (d : 𝓞 K) (q : ArchimedeanTraceTorus K) :=
    compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q)
  let g (q : ArchimedeanTraceTorus K) : ℂ :=
    ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ)
  have hcE (d : 𝓞 K) : Continuous (E d) :=
    (compactTraceNonzeroCubicSum_continuous _ _ _ _).comp (traceTorusMul_continuous d)
  have hcg : Continuous g := Complex.continuous_ofReal.comp
    (((compactTraceWeylSum_continuous _ _ _ _ _).comp (traceTorusMul_continuous 4)).norm.pow 4)
  unfold compactMixedJIntegral
  simp_rw [compactMixedJIntegrand_expansion]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro p _
    simpa only [mul_assoc,E,g] using
      (integral_const_mul
        (w (M⁻¹ • mixedEmbedding K ((p.1:𝓞 K):K))*
          conj (w (M⁻¹ • mixedEmbedding K ((p.2:𝓞 K):K))))
        (fun q => E ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) q*g q) (μ:=traceHaar))
  · intro p _
    exact ((continuous_const.mul (hcE ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6))).mul hcg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem norm_cubic_cross_integral_le_K (u v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hvc : HasCompactSupport v)
    (H R : ℝ) (hH : H ≠ 0) (hR : R ≠ 0) (d : 𝓞 K) :
    ‖∫ q, compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q) *
      ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ) ∂traceHaar‖ ≤
      mixedKIntegral u v huc hvc H R hH hR d := by
  have h := norm_integral_le_integral_norm (μ:=traceHaar)
    (fun q => compactTraceNonzeroCubicSum u huc H hH (traceTorusMul d q) *
      ((‖compactTraceWeylSum 3 v hvc R hR (traceTorusMul 4 q)‖^4 : ℝ):ℂ))
  simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (norm_nonneg _) _)] using h

/-- The full J reduction is a proved triangle inequality on its exact
sixth-power pair expansion. No positivity of its complex integrand is used. -/
theorem compactMixedJIntegral_le_pairK (u w v : mixedSpace K → ℂ)
    (huc : HasCompactSupport u) (hwc : HasCompactSupport w) (hvc : HasCompactSupport v)
    (H M R : ℝ) (hH : H ≠ 0) (hM : M ≠ 0) (hR : R ≠ 0) :
    ‖compactMixedJIntegral u w v huc hwc hvc H M R hH hM hR‖ ≤
      ∑ p : compactIntegerSupport w hwc M hM × compactIntegerSupport w hwc M hM,
        (‖w (M⁻¹ • mixedEmbedding K ((p.1:𝓞 K):K))‖*
          ‖w (M⁻¹ • mixedEmbedding K ((p.2:𝓞 K):K))‖) *
          mixedKIntegral u v huc hvc H R hH hR ((p.1:𝓞 K)^6-(p.2:𝓞 K)^6) := by
  rw [compactMixedJIntegral_expansion]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p _
  rw [norm_mul,norm_mul,Complex.norm_conj]
  exact mul_le_mul_of_nonneg_left (norm_cubic_cross_integral_le_K _ _ _ _ _ _ _ _ _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))

end WaringSiegel.WSL3Poisson
